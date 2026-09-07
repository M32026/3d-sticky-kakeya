import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TerminalPacketDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRescaling
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex

/-!
# Proposition 6.2: pure CWA on terminal complete metric fibers

The four-degree regularization selects terminal metric parents and then keeps
their complete metric fibers as tube families.  Hence a terminal complete
fiber is not an arbitrary subfamily of an ambient fiber: it is exactly the
same ambient complete fiber with a different finite indexing.

This module isolates the minimal upstream input, namely pure nearby CWA on
each ambient complete metric fiber, and transports it to the corresponding
complete fiber of the final fine family using
`TerminalCompleteFamiliesData.fine_complete`.
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

namespace TerminalCompleteFamiliesData

/-- The ambient complete metric fiber, with its canonical finite indexing. -/
noncomputable def ambientFiber
    (_families :
      input.TerminalCompleteFamiliesData
        multiplicity parentClass treeCleanup exactification
          core.ranges)
    (parent : Fin coarse.card) :
    Kakeya.Streamlined.TubeSubfamily fine :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset fine
    (wz2PaperFullFiberIndices fine coarse parent)

/-- The corresponding complete metric fiber inside the final fine family. -/
noncomputable def terminalFiber
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    Kakeya.Streamlined.TubeSubfamily
      families.restriction.fineSelected.family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    families.restriction.fineSelected.family
    (wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent)

/-- Exact ambient-index map from a terminal complete-fiber member to the
corresponding ambient complete-fiber member. -/
noncomputable def terminalFiberMemberToAmbient
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    {source : Fin
        families.restriction.fineSelected.family.card //
      source ∈
        wz2PaperFullFiberIndices
          families.restriction.fineSelected.family
          families.restriction.coarseSelected.family parent} →
      {source : Fin fine.card //
        source ∈
          wz2PaperFullFiberIndices fine coarse
            (families.restriction.coarseSelected.embedding parent)} :=
  fun source =>
    ⟨families.restriction.fineSelected.embedding source.1, by
      have sourceImage :
          families.restriction.fineSelected.embedding source.1 ∈
            Finset.image
              families.restriction.fineSelected.embedding
              (wz2PaperFullFiberIndices
                families.restriction.fineSelected.family
                families.restriction.coarseSelected.family parent) :=
        Finset.mem_image.mpr ⟨source.1, source.2, rfl⟩
      rw [families.fine_complete parent] at sourceImage
      exact sourceImage⟩

theorem terminalFiberMemberToAmbient_bijective
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    Function.Bijective
      (families.terminalFiberMemberToAmbient
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent) := by
  constructor
  · intro first second equality
    apply Subtype.ext
    apply families.restriction.fineSelected.embedding.injective
    exact congrArg Subtype.val equality
  · intro ambientSource
    have sourceImage :
        ambientSource.1 ∈
          Finset.image
            families.restriction.fineSelected.embedding
            (wz2PaperFullFiberIndices
              families.restriction.fineSelected.family
              families.restriction.coarseSelected.family parent) := by
      rw [families.fine_complete parent]
      exact ambientSource.2
    rcases Finset.mem_image.mp sourceImage with
      ⟨source, sourceMem, sourceEq⟩
    refine ⟨⟨source, sourceMem⟩, ?_⟩
    exact Subtype.ext sourceEq

/-- The exact finite equivalence between final and ambient complete fibers. -/
noncomputable def terminalFiberIndexEquiv
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    Fin
        (families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).family.card ≃
      Fin
        (families.ambientFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core
            (families.restriction.coarseSelected.embedding parent)
        ).family.card := by
  let terminalIndices :=
    wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent
  let ambientIndices :=
    wz2PaperFullFiberIndices fine coarse
      (families.restriction.coarseSelected.embedding parent)
  let memberEquiv : terminalIndices ≃ ambientIndices :=
    Equiv.ofBijective
      (families.terminalFiberMemberToAmbient
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent)
      (families.terminalFiberMemberToAmbient_bijective
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent)
  exact
    (terminalIndices.orderIsoOfFin rfl).toEquiv |>.trans
      (memberEquiv.trans
        (ambientIndices.orderIsoOfFin rfl).symm.toEquiv)

theorem terminalFiberIndexEquiv_ambient
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (source :
      Fin
        (families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).family.card) :
    families.restriction.fineSelected.embedding
        ((families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).embedding source) =
      (families.ambientFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core
          (families.restriction.coarseSelected.embedding parent)
        ).embedding
        (families.terminalFiberIndexEquiv
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent source) := by
  let terminalIndices :=
    wz2PaperFullFiberIndices
      families.restriction.fineSelected.family
      families.restriction.coarseSelected.family parent
  let ambientIndices :=
    wz2PaperFullFiberIndices fine coarse
      (families.restriction.coarseSelected.embedding parent)
  let memberEquiv : terminalIndices ≃ ambientIndices :=
    Equiv.ofBijective
      (families.terminalFiberMemberToAmbient
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent)
      (families.terminalFiberMemberToAmbient_bijective
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent)
  let terminalMember : terminalIndices :=
    terminalIndices.orderIsoOfFin rfl source
  have ambientRoundTrip :
      (ambientIndices.orderIsoOfFin rfl)
          ((ambientIndices.orderIsoOfFin rfl).symm
            (memberEquiv terminalMember)) =
        memberEquiv terminalMember :=
    (ambientIndices.orderIsoOfFin rfl).apply_symm_apply _
  change
    families.restriction.fineSelected.embedding terminalMember.1 =
      ((ambientIndices.orderIsoOfFin rfl)
        ((ambientIndices.orderIsoOfFin rfl).symm
          (memberEquiv terminalMember))).1
  rw [ambientRoundTrip]
  rfl

theorem terminalFiber_tube_eq
    (parent :
      Fin families.restriction.coarseSelected.family.card)
    (source :
      Fin
        (families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).family.card) :
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).family.tube source =
      (families.ambientFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core
          (families.restriction.coarseSelected.embedding parent)
        ).family.tube
        (families.terminalFiberIndexEquiv
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent source) := by
  rw [
    (families.terminalFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent).tube_eq,
    (families.ambientFiber
      input multiplicity parentClass treeCleanup exactification
        parentDegree core
        (families.restriction.coarseSelected.embedding parent)
      ).tube_eq,
    families.restriction.fineSelected.tube_eq,
    families.terminalFiberIndexEquiv_ambient
      input multiplicity parentClass treeCleanup exactification
        parentDegree core parent source
  ]

structure TerminalPublicRescalingData
    (rho_le_one : rho ≤ 1)
    (sourceConstant : ENNReal) where
  ambient :
    ∀ parent ∈ families.terminalParents,
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant

namespace TerminalPublicRescalingData

variable
    {rho_le_one : rho ≤ 1}
    {sourceConstant : ENNReal}
    (data :
      families.TerminalPublicRescalingData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core rho_le_one sourceConstant)

noncomputable def reindexData
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    PureWZ2Prop62PublicRescalingReindexData
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family
      (families.restriction.coarseSelected.family.tube parent)
      input.rho_pos rho_le_one
      (families.restriction.section6Cover.fine_line_class.subfamily
        (families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent))
      (families.restriction.section6Cover.coarse_line_class parent)
      (fun source => by
        rw [(families.terminalFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).tube_eq]
        exact
          (mem_wz2PaperFullFiberIndices_iff
            parent
            ((families.terminalFiber
              input multiplicity parentClass treeCleanup exactification
                parentDegree core parent).embedding source)).mp <|
            Finset.orderEmbOfFin_mem
              (wz2PaperFullFiberIndices
                families.restriction.fineSelected.family
                families.restriction.coarseSelected.family parent)
              rfl source)
      sourceConstant := by
  let ambientParent :=
    families.restriction.coarseSelected.embedding parent
  let ambientInput :=
    data.ambient ambientParent <| by
      rw [← families.coarse_image_univ]
      exact Finset.mem_image.mpr
        ⟨parent, Finset.mem_univ parent, rfl⟩
  let ambientIndices :=
    wz2PaperFullFiberIndices fine coarse ambientParent
  let ambientEnum :
      Fin
          (families.ambientFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core ambientParent).family.card ≃
        ambientIndices :=
    (ambientIndices.orderIsoOfFin rfl).toEquiv
  have sourceIndicesEq :
      ambientInput.sourceIndices = ambientIndices := by
    exact ambientInput.sourceIndices_eq
  let ambientMemberEquiv :
      ambientIndices ≃ ambientInput.sourceIndices :=
    {
      toFun := fun index =>
        ⟨index.1, by
          rw [sourceIndicesEq]
          exact index.2⟩
      invFun := fun index =>
        ⟨index.1, by
          rw [← sourceIndicesEq]
          exact index.2⟩
      left_inv := fun _ => by ext; rfl
      right_inv := fun _ => by ext; rfl
    }
  let ambientToSource :
      Fin
          (families.ambientFiber
            input multiplicity parentClass treeCleanup exactification
              parentDegree core ambientParent).family.card ≃
        Fin ambientInput.sourceFamily.card :=
    ambientEnum.trans
      (ambientMemberEquiv.trans ambientInput.sourceEquiv.symm)
  exact
    {
      ambientFine := fine
      ambientCoarse := coarse
      ambientCover := cover
      ambientParent := ambientParent
      anchor_eq := by
        exact (families.restriction.coarseSelected.tube_eq parent).symm
      input := ambientInput
      indexEquiv :=
        (families.terminalFiberIndexEquiv
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).trans
          ambientToSource
      tube_eq := by
        intro source
        rw [families.terminalFiber_tube_eq
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent source]
        rw [(families.ambientFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core ambientParent).tube_eq]
        rw [ambientInput.source_tube_eq]
        congr 2
        let ambientMember :=
          ambientEnum
            (families.terminalFiberIndexEquiv
              input multiplicity parentClass treeCleanup exactification
                parentDegree core parent source)
        have roundTrip :
            ambientInput.sourceEquiv
                (ambientInput.sourceEquiv.symm
                  (ambientMemberEquiv ambientMember)) =
              ambientMemberEquiv ambientMember :=
          ambientInput.sourceEquiv.apply_symm_apply
            (ambientMemberEquiv ambientMember)
        change ambientMember.1 =
          (ambientInput.sourceEquiv
            (ambientInput.sourceEquiv.symm
              (ambientMemberEquiv ambientMember))).1
        rw [roundTrip]
        rfl
    }

theorem publicPureCWA
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ2PaperPureCWAAtNearbyScales
      (reindexData
        (input := input)
        (multiplicity := multiplicity)
        (parentClass := parentClass)
        (treeCleanup := treeCleanup)
        (exactification := exactification)
        (parentDegree := parentDegree)
        (core := core)
        (families := families)
        data parent).targetCertificate.publicFamily
      ((81000000 : ENNReal) * sourceConstant) :=
  PureWZ2Prop62PublicRescalingReindexData.publicPureCWA
    (reindexData
      (input := input)
      (multiplicity := multiplicity)
      (parentClass := parentClass)
      (treeCleanup := treeCleanup)
      (exactification := exactification)
      (parentDegree := parentDegree)
      (core := core)
      (families := families)
      data parent)

end TerminalPublicRescalingData

/-- Minimal upstream complete-fiber CWA certificate. -/
structure AmbientFiberCWAData
    (fiberConstant : ENNReal) : Prop where
  cwa :
    ∀ parent ∈ families.terminalParents,
      WZ2PaperPureCWAAtNearbyScales
        (families.ambientFiber
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent).family
        fiberConstant

/-- Every final complete metric fiber inherits the ambient complete-fiber CWA
by exact finite reindexing. -/
theorem terminal_fiber_pure_cwa
    {fiberConstant : ENNReal}
    (ambient :
      families.AmbientFiberCWAData
        input multiplicity parentClass treeCleanup exactification
          parentDegree core fiberConstant)
    (parent :
      Fin families.restriction.coarseSelected.family.card) :
    WZ2PaperPureCWAAtNearbyScales
      (families.terminalFiber
        input multiplicity parentClass treeCleanup exactification
          parentDegree core parent).family
      fiberConstant := by
  have parentMem :
      families.restriction.coarseSelected.embedding parent ∈
        families.terminalParents := by
    rw [← families.coarse_image_univ]
    exact
      Finset.mem_image.mpr
        ⟨parent, Finset.mem_univ _, rfl⟩
  exact
    (ambient.cwa
      (families.restriction.coarseSelected.embedding parent)
      parentMem).reindex
        (families.terminalFiberIndexEquiv
          input multiplicity parentClass treeCleanup exactification
            parentDegree core parent)
        (fun source =>
          families.terminalFiber_tube_eq
            input multiplicity parentClass treeCleanup exactification
              parentDegree core parent source)

end TerminalCompleteFamiliesData

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
