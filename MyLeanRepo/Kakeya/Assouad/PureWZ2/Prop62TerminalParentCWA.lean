import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalParentTreeDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ScheduledCoreFiberRatio
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FinitePureNearbyAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex

/-!
# Proposition 6.2: pure nearby CWA on the terminal parent family

The terminal metric parents are a complete vertex selection inside the
parent-family pure schedule.  The combined first-tree and second-peeling
node-density coefficient is `2^L * A0`.  At every scheduled scale this gives
an explicit ambient/terminal strict-fiber ratio, hence a restricted pure
scale witness.  The original finite rounding then restores nearby-scale CWA.

The construction first uses the canonical `fromFinset` terminal parent
family.  An exact ambient-index equivalence transports the result to the
terminal coarse family used by the balanced Section 6 cover.
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
    (families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
        core.ranges)

def terminalParentPure :
    WZ2PaperPureTubeSubfamily coarse :=
  WZ2PaperPureTubeSubfamily.fromFinset
    coarse families.terminalParents

def terminalDensityLoss
    (_treeCleanup :
      input.ParentTreeCleanupData
        multiplicity parentClass schedule)
    (_exactification :
      input.PacketCellExactificationData
        multiplicity parentClass _treeCleanup)
    (_parentDegree :
      input.ReferenceParentDegreeData
        multiplicity parentClass _treeCleanup _exactification)
    {bins :
      _exactification.incidence.ThreeDegreeBinningData
        _exactification.incidence.allEdges}
    {A0 : ℕ}
    (_core :
      input.FourDegreeCoreAssemblyData
        multiplicity parentClass _treeCleanup
        _exactification _parentDegree bins A0) :
    ENNReal :=
  ((2 ^ schedule.levelCount * A0 : ℕ) : ENNReal) *
    coarse.enncard *
    (parentClass.selectedParents.card : ENNReal)⁻¹

def terminalParentScaleConstant : ENNReal :=
  input.terminalDensityLoss
      multiplicity parentClass treeCleanup exactification
      parentDegree core *
    ambientConstant

def terminalParentOutputConstant : ENNReal :=
  max scaleWindow
    (input.terminalParentScaleConstant
      multiplicity parentClass treeCleanup exactification
      parentDegree core)

theorem terminalParentPure_nonempty :
    (input.terminalParentPure
      multiplicity parentClass treeCleanup exactification
      parentDegree core families).family.Nonempty := by
  change 0 < families.terminalParents.card
  rw [families.terminalParents_eq]
  have terminalNonempty :
      core.ranges.terminalEdges.Nonempty := by
    change core.ranges.peeling.core.Nonempty
    rw [core.ranges_peeling_eq]
    exact core.core_nonempty
  exact
    (input.terminalParentIndices_nonempty
      multiplicity parentClass treeCleanup exactification
      core.ranges terminalNonempty).card_pos

theorem terminalParents_subset_selectedParents :
    families.terminalParents ⊆ parentClass.selectedParents := by
  intro parent parentMem
  have terminalMem :
      parent ∈
        input.terminalParentIndices
          multiplicity parentClass treeCleanup exactification
          core.ranges := by
    rwa [families.terminalParents_eq] at parentMem
  exact
    treeCleanup.referenceParents_subset <|
      input.terminalParent_mem_reference
        multiplicity parentClass treeCleanup exactification
        parentDegree core terminalMem

theorem terminal_scheduled_fiber_ratio
    (coordinate : Fin schedule.levelCount)
    (parent :
      Fin
        ((schedule.scaleData coordinate).cover.hitParentSubfamily
          (input.terminalParentPure
            multiplicity parentClass treeCleanup exactification
            parentDegree core families)).family.card) :
    wz2PaperOrdinaryFullFiberCount
        coarse
        (schedule.scaleData coordinate).coarse
        (((schedule.scaleData coordinate).cover.hitParentSubfamily
          (input.terminalParentPure
            multiplicity parentClass treeCleanup exactification
            parentDegree core families)).embedding parent) ≤
      input.terminalDensityLoss
          multiplicity parentClass treeCleanup exactification
          parentDegree core *
        wz2PaperOrdinaryFullFiberCount
          (input.terminalParentPure
            multiplicity parentClass treeCleanup exactification
            parentDegree core families).family
          ((schedule.scaleData coordinate).cover.hitParentSubfamily
            (input.terminalParentPure
              multiplicity parentClass treeCleanup exactification
              parentDegree core families)).family
          parent := by
  apply
    schedule.selectedFullFiber_count_le_of_core_densityConstant
      coordinate
      (2 ^ schedule.levelCount * A0)
      parentClass.selectedParents_nonempty
      ?_
      ?_
      parent
  · intro terminalParent terminalMem
    exact
      input.terminalParents_subset_selectedParents
        multiplicity parentClass treeCleanup exactification
        parentDegree core families terminalMem
  · intro node nodeNonempty
    have levelLe :
        coordinate.1 + 1 ≤ schedule.levelCount := by
      omega
    have terminalNodeNonempty :
        (input.terminalParentsAtNode
          multiplicity parentClass treeCleanup exactification
          parentDegree core (coordinate.1 + 1) node).Nonempty := by
      simpa [
        terminalParentsAtNode,
        families.terminalParents_eq
      ] using nodeNonempty
    simpa [
      terminalParentsAtNode,
      families.terminalParents_eq
    ] using
      input.terminal_node_density
        multiplicity parentClass treeCleanup exactification
        parentDegree core levelLe node terminalNodeNonempty

theorem terminal_scheduled_fiber_uniform
    (coordinate : Fin schedule.levelCount) :
    WZ2PaperPureFullFibersAreCUniform
      (input.terminalParentPure
        multiplicity parentClass treeCleanup exactification
        parentDegree core families).family
      ((schedule.scaleData coordinate).cover.hitParentSubfamily
        (input.terminalParentPure
          multiplicity parentClass treeCleanup exactification
          parentDegree core families)).family
      (input.terminalParentScaleConstant
        multiplicity parentClass treeCleanup exactification
        parentDegree core) := by
  intro first second
  let selected :=
    input.terminalParentPure
      multiplicity parentClass treeCleanup exactification
      parentDegree core families
  let selectedCoarse :=
    (schedule.scaleData coordinate).cover.hitParentSubfamily selected
  have selectedLeAmbient :
      wz2PaperOrdinaryFullFiberCount
          selected.family selectedCoarse.family first ≤
        wz2PaperOrdinaryFullFiberCount
          coarse (schedule.scaleData coordinate).coarse
          (selectedCoarse.embedding first) := by
    rw [
      wz2PaperOrdinaryFullFiberCount,
      wz2PaperOrdinaryFullFiberCount,
      wz2_paper_selected_fullFiber_card
    ]
    have selectedSubset :
        wz2PaperSelectedAmbientFullFiberIndices
            selected (selectedCoarse.embedding first) ⊆
          wz2PaperOrdinaryFullFiberIndices
            coarse (schedule.scaleData coordinate).coarse
              (selectedCoarse.embedding first) := by
      intro source sourceMem
      exact (Finset.mem_filter.mp sourceMem).2.2
    exact_mod_cast Finset.card_le_card selectedSubset
  calc
    wz2PaperOrdinaryFullFiberCount
        selected.family selectedCoarse.family first ≤
      wz2PaperOrdinaryFullFiberCount
        coarse (schedule.scaleData coordinate).coarse
        (selectedCoarse.embedding first) :=
      selectedLeAmbient
    _ ≤
      ambientConstant *
        wz2PaperOrdinaryFullFiberCount
          coarse (schedule.scaleData coordinate).coarse
          (selectedCoarse.embedding second) :=
      (schedule.scaleData coordinate).full_fiber_uniform _ _
    _ ≤
      ambientConstant *
        (input.terminalDensityLoss
            multiplicity parentClass treeCleanup exactification
            parentDegree core *
          wz2PaperOrdinaryFullFiberCount
            selected.family selectedCoarse.family second) := by
      gcongr
      exact
        input.terminal_scheduled_fiber_ratio
          multiplicity parentClass treeCleanup exactification
          parentDegree core families coordinate second
    _ =
      input.terminalParentScaleConstant
          multiplicity parentClass treeCleanup exactification
          parentDegree core *
        wz2PaperOrdinaryFullFiberCount
          selected.family selectedCoarse.family second := by
      simp only [terminalParentScaleConstant]
      ring

noncomputable def terminalScaleData
    (coordinate : Fin schedule.levelCount) :
    WZ2PaperPureScaleCoverData
      (input.terminalParentPure
        multiplicity parentClass treeCleanup exactification
        parentDegree core families).family
      (schedule.actualScale coordinate)
      (input.terminalParentScaleConstant
        multiplicity parentClass treeCleanup exactification
        parentDegree core) := by
  let selected :=
    input.terminalParentPure
      multiplicity parentClass treeCleanup exactification
      parentDegree core families
  let selectedCoarse :=
    (schedule.scaleData coordinate).cover.hitParentSubfamily selected
  let restrictedCover :=
    (schedule.scaleData coordinate).cover.restrictToHitParents selected
  let restricted :=
    (schedule.scaleData coordinate).restrict
      selected selectedCoarse restrictedCover
      (input.terminal_scheduled_fiber_uniform
        multiplicity parentClass treeCleanup exactification
        parentDegree core families coordinate)
      (input.terminal_scheduled_fiber_ratio
        multiplicity parentClass treeCleanup exactification
        parentDegree core families coordinate)
  simpa only [
    terminalParentScaleConstant,
    max_self,
    mul_comm
  ] using restricted

theorem terminalDensityLoss_ne_top :
    input.terminalDensityLoss
      multiplicity parentClass treeCleanup exactification
      parentDegree core ≠ ⊤ := by
  have selectedCardNeZero :
      (parentClass.selectedParents.card : ENNReal) ≠ 0 := by
    exact_mod_cast parentClass.selectedParents_nonempty.card_pos.ne'
  exact
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top (2 ^ schedule.levelCount * A0))
        (by simp [Kakeya.Streamlined.TubeFamily.enncard]))
      (ENNReal.inv_ne_top.mpr selectedCardNeZero)

theorem terminalParentOutputConstant_finite :
    WZ2PaperFiniteErrorConstant
      (input.terminalParentOutputConstant
        multiplicity parentClass treeCleanup exactification
        parentDegree core) := by
  have scaleConstantFinite :
      input.terminalParentScaleConstant
        multiplicity parentClass treeCleanup exactification
        parentDegree core ≠ ⊤ :=
    ENNReal.mul_ne_top
      (input.terminalDensityLoss_ne_top
        multiplicity parentClass treeCleanup exactification
        parentDegree core)
      schedule.ambient_finite.2
  exact
    ⟨schedule.scaleWindow_finite.1.trans
        (le_max_left _ _),
      max_ne_top schedule.scaleWindow_finite.2
        scaleConstantFinite⟩

theorem terminalParentPureCWA :
    WZ2PaperPureCWAAtNearbyScales
      (input.terminalParentPure
        multiplicity parentClass treeCleanup exactification
        parentDegree core families).family
      (input.terminalParentOutputConstant
        multiplicity parentClass treeCleanup exactification
        parentDegree core) := by
  apply pureWZ2_nearby_from_finite_witnesses
    (schedule.scaleData ⟨0, schedule.levelCount_pos⟩).delta_pos
    (input.terminalParentOutputConstant_finite
      multiplicity parentClass treeCleanup exactification
      parentDegree core).1
    (input.terminalParentOutputConstant_finite
      multiplicity parentClass treeCleanup exactification
      parentDegree core).2
    (schedule.fine_distinct.subfamily
      (input.terminalParentPure
        multiplicity parentClass treeCleanup exactification
          parentDegree core families))
    schedule.levelCount schedule.levelCount_pos
    (fun coordinate =>
      ⟨schedule.actualScale coordinate,
        (input.terminalScaleData
          multiplicity parentClass treeCleanup exactification
          parentDegree core families coordinate).mono
            (le_max_right _ _)⟩)
  intro requested
  rcases schedule.rounding requested with
    ⟨coordinate, requestedLe, withinFactor⟩
  exact
    ⟨coordinate, requestedLe,
      withinFactor.trans_le <| by
        gcongr
        exact le_max_left _ _⟩

noncomputable def terminalParentIndexEquiv :
    Fin families.restriction.coarseSelected.family.card ≃
      Fin
        (input.terminalParentPure
          multiplicity parentClass treeCleanup exactification
          parentDegree core families).family.card := by
  let canonical :=
    input.terminalParentPure
      multiplicity parentClass treeCleanup exactification
      parentDegree core families
  let canonicalEquiv :
      Fin canonical.family.card ≃ families.terminalParents :=
    (families.terminalParents.orderIsoOfFin rfl).toEquiv
  let finalToTerminal :
      Fin families.restriction.coarseSelected.family.card →
        families.terminalParents :=
    fun parent =>
      ⟨families.restriction.coarseSelected.embedding parent, by
        rw [← families.coarse_image_univ]
        exact
          Finset.mem_image.mpr
            ⟨parent, Finset.mem_univ _, rfl⟩⟩
  have finalInjective : Function.Injective finalToTerminal := by
    intro first second equality
    apply families.restriction.coarseSelected.embedding.injective
    exact congrArg Subtype.val equality
  have finalSurjective : Function.Surjective finalToTerminal := by
    intro parent
    have parentImage :
        parent.1 ∈
          Finset.image
            families.restriction.coarseSelected.embedding Finset.univ := by
      rw [families.coarse_image_univ]
      exact parent.2
    rcases Finset.mem_image.mp parentImage with
      ⟨selectedParent, _selectedUniv, parentEq⟩
    refine ⟨selectedParent, ?_⟩
    exact Subtype.ext parentEq
  exact
    (Equiv.ofBijective finalToTerminal
      ⟨finalInjective, finalSurjective⟩).trans
        canonicalEquiv.symm

theorem terminalParentIndexEquiv_ambient
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    (input.terminalParentPure
      multiplicity parentClass treeCleanup exactification
      parentDegree core families).embedding
        (input.terminalParentIndexEquiv
          multiplicity parentClass treeCleanup exactification
          parentDegree core families parent) =
      families.restriction.coarseSelected.embedding parent := by
  let canonical :=
    input.terminalParentPure
      multiplicity parentClass treeCleanup exactification
      parentDegree core families
  let canonicalEquiv :
      Fin canonical.family.card ≃ families.terminalParents :=
    (families.terminalParents.orderIsoOfFin rfl).toEquiv
  let finalToTerminal :
      Fin families.restriction.coarseSelected.family.card →
        families.terminalParents :=
    fun selectedParent =>
      ⟨families.restriction.coarseSelected.embedding selectedParent, by
        rw [← families.coarse_image_univ]
        exact
          Finset.mem_image.mpr
            ⟨selectedParent, Finset.mem_univ _, rfl⟩⟩
  have finalInjective : Function.Injective finalToTerminal := by
    intro first second equality
    apply families.restriction.coarseSelected.embedding.injective
    exact congrArg Subtype.val equality
  have finalSurjective : Function.Surjective finalToTerminal := by
    intro terminalParent
    have parentImage :
        terminalParent.1 ∈
          Finset.image
            families.restriction.coarseSelected.embedding Finset.univ := by
      rw [families.coarse_image_univ]
      exact terminalParent.2
    rcases Finset.mem_image.mp parentImage with
      ⟨selectedParent, _selectedUniv, parentEq⟩
    refine ⟨selectedParent, ?_⟩
    exact Subtype.ext parentEq
  have canonicalRoundTrip :
      canonicalEquiv (canonicalEquiv.symm
        ((Equiv.ofBijective finalToTerminal
          ⟨finalInjective, finalSurjective⟩) parent)) =
        (Equiv.ofBijective finalToTerminal
          ⟨finalInjective, finalSurjective⟩) parent :=
    canonicalEquiv.apply_symm_apply _
  change
    (canonicalEquiv
      (canonicalEquiv.symm
        ((Equiv.ofBijective finalToTerminal
          ⟨finalInjective, finalSurjective⟩) parent))).1 =
      families.restriction.coarseSelected.embedding parent
  rw [canonicalRoundTrip, Equiv.ofBijective_apply]

theorem terminalParent_tube_eq
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    families.restriction.coarseSelected.family.tube parent =
      (input.terminalParentPure
        multiplicity parentClass treeCleanup exactification
        parentDegree core families).family.tube
          (input.terminalParentIndexEquiv
            multiplicity parentClass treeCleanup exactification
            parentDegree core families parent) := by
  rw [
    families.restriction.coarseSelected.tube_eq,
    (input.terminalParentPure
      multiplicity parentClass treeCleanup exactification
      parentDegree core families).tube_eq,
    input.terminalParentIndexEquiv_ambient
      multiplicity parentClass treeCleanup exactification
      parentDegree core families parent
  ]

theorem terminalParentCWA :
    WZ2PaperPureCWAAtNearbyScales
      families.restriction.coarseSelected.family
      (input.terminalParentOutputConstant
        multiplicity parentClass treeCleanup exactification
        parentDegree core) := by
  exact
    (input.terminalParentPureCWA
      multiplicity parentClass treeCleanup exactification
      parentDegree core families).reindex
        (input.terminalParentIndexEquiv
          multiplicity parentClass treeCleanup exactification
          parentDegree core families)
        (input.terminalParent_tube_eq
          multiplicity parentClass treeCleanup exactification
          parentDegree core families)

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
