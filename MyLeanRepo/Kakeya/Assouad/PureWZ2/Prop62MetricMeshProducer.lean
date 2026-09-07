import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CompleteParentScale

/-!
# Proposition 6.2 metric parents: selected mesh-cell producer

After one weighted residue-color selection, keep a nonempty set of occupied
line-parameter cells.  Each selected cell chooses one old scale parent as its
representative.  All old strict packets in that cell are kept whole, and the
centered exact radius-`rho` tube on the representative axis is the new metric
parent.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62SelectedMeshCells
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    (width : ℝ) where
  rho_pos : 0 < rho
  fine_nonempty : fine.Nonempty
  selectedParents : Finset (Fin oldData.coarse.card)
  selectedParents_nonempty : selectedParents.Nonempty
  representative :
    (Fin 4 → ℤ) → Fin oldData.coarse.card
  representative_mem :
    ∀ cell ∈
        Finset.image
          (fun parent =>
            pureWZ2Prop62LineCell width
              (oldData.coarse.tube parent))
          selectedParents,
      representative cell ∈ selectedParents ∧
        pureWZ2Prop62LineCell width
            (oldData.coarse.tube (representative cell)) =
          cell

theorem exists_pureWZ2Prop62SelectedMeshCells
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    (width : ℝ)
    (rhoPos : 0 < rho)
    (fineNonempty : fine.Nonempty)
    (selectedParents : Finset (Fin oldData.coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty) :
    ∃ mesh :
        PureWZ2Prop62SelectedMeshCells
          (rho := rho) oldData width,
      mesh.selectedParents = selectedParents := by
  let occupiedCells : Finset (Fin 4 → ℤ) :=
    Finset.image
      (fun parent =>
        pureWZ2Prop62LineCell width
          (oldData.coarse.tube parent))
      selectedParents
  let defaultParent : Fin oldData.coarse.card :=
    Classical.choose selectedParentsNonempty
  let representative : (Fin 4 → ℤ) → Fin oldData.coarse.card :=
    fun cell =>
      if hcell : cell ∈ occupiedCells then
        Classical.choose (Finset.mem_image.mp hcell)
      else
        defaultParent
  refine
    ⟨{
      rho_pos := rhoPos
      fine_nonempty := fineNonempty
      selectedParents := selectedParents
      selectedParents_nonempty := selectedParentsNonempty
      representative := representative
      representative_mem := ?_
    }, rfl⟩
  intro cell hcell
  have hoccupied : cell ∈ occupiedCells := by
    exact hcell
  have chosen :=
    Classical.choose_spec (Finset.mem_image.mp hoccupied)
  change
    representative cell ∈ selectedParents ∧
      pureWZ2Prop62LineCell width
          (oldData.coarse.tube (representative cell)) =
        cell
  rw [show representative cell =
      Classical.choose (Finset.mem_image.mp hoccupied) by
    simp only [representative, dif_pos hoccupied]]
  exact chosen

namespace PureWZ2Prop62SelectedMeshCells

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width : ℝ}
    {M : ℝ}
    (mesh :
      PureWZ2Prop62SelectedMeshCells
        (rho := rho) oldData width)

def occupiedCells : Finset (Fin 4 → ℤ) :=
  Finset.image
    (fun parent =>
      pureWZ2Prop62LineCell width
        (oldData.coarse.tube parent))
    mesh.selectedParents

noncomputable def cellEquiv :
    Fin mesh.occupiedCells.card ≃ mesh.occupiedCells :=
  by
    simpa using (Fintype.equivFin mesh.occupiedCells).symm

noncomputable def coarse :
    Kakeya.Streamlined.TubeFamily rho where
  card := mesh.occupiedCells.card
  tube cell :=
    wz2PaperCenteredLineTube
      (targetScale := rho)
      (oldData.coarse.tube
        (mesh.representative (mesh.cellEquiv cell)))

noncomputable def complete :
    PureWZ2CompleteParentRestrictionData
      oldData.cover mesh.selectedParents :=
  PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
    oldData.cover mesh.selectedParents mesh.selectedParents_nonempty

noncomputable def restrictedOldData :
    WZ2PaperPureScaleCoverData
      mesh.complete.selectedFine.family scale C :=
  pureWZ2_prop62_completeParent_sameScale
    oldData mesh.selectedParents mesh.selectedParents_nonempty

noncomputable def selectedOldCoarse :
    WZ2PaperPureTubeSubfamily oldData.coarse :=
  oldData.cover.hitParentSubfamily mesh.complete.selectedFine

theorem restrictedOldData_coarse_eq :
    mesh.restrictedOldData.coarse =
      mesh.selectedOldCoarse.family := by
  exact
    pureWZ2_prop62_completeParent_sameScale_coarse
      oldData mesh.selectedParents mesh.selectedParents_nonempty

theorem restrictedOldData_parent_ambient
    (source : Fin mesh.complete.selectedFine.family.card) :
    mesh.selectedOldCoarse.embedding
        (mesh.restrictedOldData.cover.parent source) =
      oldData.cover.parent
        (mesh.complete.selectedFine.embedding source) := by
  change
    (oldData.cover.hitParentSubfamily
      mesh.complete.selectedFine).embedding
        (mesh.restrictedOldData.cover.parent source) =
      oldData.cover.parent
        (mesh.complete.selectedFine.embedding source)
  exact
    pureWZ2_prop62_completeParent_sameScale_parent_ambient
      oldData mesh.selectedParents mesh.selectedParents_nonempty source

theorem selectedOldCoarse_parent_mem
    (parent : Fin mesh.selectedOldCoarse.family.card) :
    mesh.selectedOldCoarse.embedding parent ∈
      mesh.selectedParents := by
  rcases oldData.cover.hitParent_surjective
      mesh.complete.selectedFine parent with
    ⟨source, hsource⟩
  have hselected :=
    mesh.complete.selectedFine_parent_mem source
  rw [← oldData.cover.hitParent_ambient
    mesh.complete.selectedFine source, hsource] at hselected
  exact hselected

theorem selectedOldCoarse_surjective_on_selectedParents :
    ∀ ambientParent ∈ mesh.selectedParents,
      ∃ parent : Fin mesh.selectedOldCoarse.family.card,
        mesh.selectedOldCoarse.embedding parent = ambientParent := by
  intro ambientParent hparent
  have fiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        fine oldData.coarse ambientParent).Nonempty :=
    oldData.cover.fullFiber_nonempty_of_uniform
      mesh.fine_nonempty oldData.full_fiber_uniform ambientParent
  rcases fiberNonempty with ⟨ambientSource, hsource⟩
  have selectedMem :
      ambientSource ∈ mesh.complete.selectedFineIndices := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ ambientSource, by
        rw [(oldData.cover.mem_fullFiber_iff_parent_eq
          oldData.rho_pos.le ambientParent ambientSource).mp hsource]
        exact hparent⟩
  rcases mesh.complete.selectedFine_ambient_surjective
      ambientSource selectedMem with
    ⟨source, sourceEq⟩
  refine
    ⟨oldData.cover.hitParent mesh.complete.selectedFine source, ?_⟩
  change
    (oldData.cover.hitParentSubfamily
      mesh.complete.selectedFine).embedding
        (oldData.cover.hitParent mesh.complete.selectedFine source) =
      ambientParent
  rw [oldData.cover.hitParent_ambient]
  rw [sourceEq]
  exact
    (oldData.cover.mem_fullFiber_iff_parent_eq
      oldData.rho_pos.le ambientParent ambientSource).mp hsource

noncomputable def oldPacketParent
    (parent : Fin mesh.selectedOldCoarse.family.card) :
    Fin mesh.coarse.card :=
  mesh.cellEquiv.symm
    ⟨pureWZ2Prop62LineCell width
        (oldData.coarse.tube
          (mesh.selectedOldCoarse.embedding parent)),
      Finset.mem_image.mpr
        ⟨mesh.selectedOldCoarse.embedding parent,
          mesh.selectedOldCoarse_parent_mem parent, rfl⟩⟩

@[simp] theorem oldPacketParent_cell
    (parent : Fin mesh.selectedOldCoarse.family.card) :
    mesh.cellEquiv (mesh.oldPacketParent parent) =
      ⟨pureWZ2Prop62LineCell width
          (oldData.coarse.tube
            (mesh.selectedOldCoarse.embedding parent)),
        Finset.mem_image.mpr
          ⟨mesh.selectedOldCoarse.embedding parent,
            mesh.selectedOldCoarse_parent_mem parent, rfl⟩⟩ :=
  mesh.cellEquiv.apply_symm_apply _

theorem oldPacketParent_surjective :
    Function.Surjective mesh.oldPacketParent := by
  intro parent
  let cell := (mesh.cellEquiv parent).1
  have cellMem : cell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv parent).2
  rcases Finset.mem_image.mp cellMem with
    ⟨ambientParent, hambientParent, hcell⟩
  rcases mesh.selectedOldCoarse_surjective_on_selectedParents
      ambientParent hambientParent with
    ⟨oldParent, holdParent⟩
  refine ⟨oldParent, ?_⟩
  apply mesh.cellEquiv.injective
  rw [mesh.oldPacketParent_cell]
  apply Subtype.ext
  change
    pureWZ2Prop62LineCell width
        (oldData.coarse.tube
          (mesh.selectedOldCoarse.embedding oldParent)) =
      (mesh.cellEquiv parent).1
  calc
    pureWZ2Prop62LineCell width
          (oldData.coarse.tube
            (mesh.selectedOldCoarse.embedding oldParent)) =
        pureWZ2Prop62LineCell width
          (oldData.coarse.tube ambientParent) := by
      rw [holdParent]
    _ = cell := hcell
    _ = (mesh.cellEquiv parent).1 := rfl

theorem oldPacketParent_representative_close
    (parent : Fin mesh.selectedOldCoarse.family.card)
    (oldLine : WZ1PaperIsLineClass oldData.coarse)
    (widthPos : 0 < width) :
    wz1PaperLineDistance
        (mesh.selectedOldCoarse.family.tube parent)
        (mesh.coarse.tube (mesh.oldPacketParent parent)) ≤
      6 * width := by
  let cell :=
    pureWZ2Prop62LineCell width
      (oldData.coarse.tube
        (mesh.selectedOldCoarse.embedding parent))
  have cellMem : cell ∈ mesh.occupiedCells :=
    Finset.mem_image.mpr
      ⟨mesh.selectedOldCoarse.embedding parent,
        mesh.selectedOldCoarse_parent_mem parent, rfl⟩
  have representativeData :=
    mesh.representative_mem cell cellMem
  rw [mesh.selectedOldCoarse.tube_eq]
  change
    wz1PaperLineDistance
        (oldData.coarse.tube
          (mesh.selectedOldCoarse.embedding parent))
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (oldData.coarse.tube
            (mesh.representative
              (mesh.cellEquiv (mesh.oldPacketParent parent))))) ≤
      6 * width
  rw [wz1PaperLineDistance_centeredLineTube_right
    (oldLine (mesh.selectedOldCoarse.embedding parent))
    (oldLine
      (mesh.representative
        (mesh.cellEquiv (mesh.oldPacketParent parent))))]
  apply pureWZ2_prop62_sameLineCell_lineDistance_le
    widthPos _ _ (oldLine _) (oldLine _)
  rw [mesh.oldPacketParent_cell]
  exact representativeData.2.symm

noncomputable def selectedOldParent
    (source : Fin mesh.complete.selectedFine.family.card) :
    Fin oldData.coarse.card :=
  oldData.cover.parent
    (mesh.complete.selectedFine.embedding source)

noncomputable def sourceCell
    (source : Fin mesh.complete.selectedFine.family.card) :
    Fin 4 → ℤ :=
  pureWZ2Prop62LineCell width
    (oldData.coarse.tube (mesh.selectedOldParent source))

theorem sourceCell_mem
    (source : Fin mesh.complete.selectedFine.family.card) :
    mesh.sourceCell source ∈ mesh.occupiedCells := by
  apply Finset.mem_image.mpr
  refine
    ⟨mesh.selectedOldParent source,
      mesh.complete.selectedFine_parent_mem source, rfl⟩

noncomputable def packetParent
    (source : Fin mesh.complete.selectedFine.family.card) :
    Fin mesh.coarse.card :=
  mesh.cellEquiv.symm
    ⟨mesh.sourceCell source, mesh.sourceCell_mem source⟩

@[simp] theorem packetParent_cell
    (source : Fin mesh.complete.selectedFine.family.card) :
    mesh.cellEquiv (mesh.packetParent source) =
      ⟨mesh.sourceCell source, mesh.sourceCell_mem source⟩ :=
  mesh.cellEquiv.apply_symm_apply _

theorem oldPacketParent_restricted_parent_eq_packetParent
    (source : Fin mesh.complete.selectedFine.family.card) :
    mesh.oldPacketParent
        (mesh.restrictedOldData.cover.parent source) =
      mesh.packetParent source := by
  apply mesh.cellEquiv.injective
  rw [mesh.oldPacketParent_cell, mesh.packetParent_cell]
  apply Subtype.ext
  change
    pureWZ2Prop62LineCell width
        (oldData.coarse.tube
          (mesh.selectedOldCoarse.embedding
            (mesh.restrictedOldData.cover.parent source))) =
      pureWZ2Prop62LineCell width
        (oldData.coarse.tube
          (oldData.cover.parent
            (mesh.complete.selectedFine.embedding source)))
  exact congrArg
    (fun parent =>
      pureWZ2Prop62LineCell width
        (oldData.coarse.tube parent))
    (mesh.restrictedOldData_parent_ambient source)

theorem packetParent_eq_iff_sourceCell_eq
    (first second : Fin mesh.complete.selectedFine.family.card) :
    mesh.packetParent first = mesh.packetParent second ↔
      mesh.sourceCell first = mesh.sourceCell second := by
  constructor
  · intro parentEq
    have cellEq := congrArg mesh.cellEquiv parentEq
    rw [mesh.packetParent_cell, mesh.packetParent_cell] at cellEq
    exact congrArg Subtype.val cellEq
  · intro cellEq
    apply mesh.cellEquiv.injective
    rw [mesh.packetParent_cell, mesh.packetParent_cell]
    apply Subtype.ext
    exact cellEq

theorem packetParent_surjective :
    Function.Surjective mesh.packetParent := by
  intro parent
  let cell := (mesh.cellEquiv parent).1
  have cellMem : cell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv parent).2
  rcases Finset.mem_image.mp cellMem with
    ⟨oldParent, oldParentMem, oldParentCell⟩
  have oldFiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        fine oldData.coarse oldParent).Nonempty :=
    oldData.cover.fullFiber_nonempty_of_uniform
      mesh.fine_nonempty oldData.full_fiber_uniform oldParent
  rcases oldFiberNonempty with ⟨ambientSource, ambientMem⟩
  have ambientParent :
      oldData.cover.parent ambientSource = oldParent :=
    (oldData.cover.mem_fullFiber_iff_parent_eq
      oldData.rho_pos.le oldParent ambientSource).mp ambientMem
  have ambientSelected :
      ambientSource ∈ mesh.complete.selectedFineIndices := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ ambientSource, by
        rw [ambientParent]
        exact oldParentMem⟩
  rcases mesh.complete.selectedFine_ambient_surjective
      ambientSource ambientSelected with
    ⟨source, sourceEq⟩
  refine ⟨source, ?_⟩
  apply mesh.cellEquiv.injective
  rw [mesh.packetParent_cell]
  apply Subtype.ext
  dsimp only [sourceCell, selectedOldParent]
  have parentEq :
      oldData.cover.parent
          (mesh.complete.selectedFine.embedding source) =
        oldParent :=
    by rw [sourceEq, ambientParent]
  rw [parentEq, oldParentCell]

theorem packetParent_representative_close
    (source : Fin mesh.complete.selectedFine.family.card)
    (oldLine : WZ1PaperIsLineClass oldData.coarse)
    (widthPos : 0 < width) :
    wz1PaperLineDistance
        (oldData.coarse.tube (mesh.selectedOldParent source))
        (mesh.coarse.tube (mesh.packetParent source)) ≤
      6 * width := by
  let cell := mesh.sourceCell source
  have cellMem : cell ∈ mesh.occupiedCells :=
    mesh.sourceCell_mem source
  have representativeData :=
    mesh.representative_mem cell cellMem
  change
    wz1PaperLineDistance
        (oldData.coarse.tube (mesh.selectedOldParent source))
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (oldData.coarse.tube
            (mesh.representative
              (mesh.cellEquiv (mesh.packetParent source))))) ≤
      6 * width
  rw [wz1PaperLineDistance_centeredLineTube_right
    (oldLine (mesh.selectedOldParent source))
    (oldLine
      (mesh.representative
        (mesh.cellEquiv (mesh.packetParent source))))]
  apply pureWZ2_prop62_sameLineCell_lineDistance_le
    widthPos
    (oldData.coarse.tube (mesh.selectedOldParent source))
    (oldData.coarse.tube
      (mesh.representative
        (mesh.cellEquiv (mesh.packetParent source))))
    (oldLine _) (oldLine _)
  rw [show
    mesh.cellEquiv (mesh.packetParent source) =
      ⟨cell, cellMem⟩ by
        exact mesh.packetParent_cell source]
  exact representativeData.2.symm

theorem coarse_line_class
    (oldLine : WZ1PaperIsLineClass oldData.coarse) :
    WZ1PaperIsLineClass mesh.coarse := by
  intro parent
  exact
    wz2PaperCenteredLineTube_lineClass
      (oldLine
        (mesh.representative (mesh.cellEquiv parent)))

theorem coarse_centered
    (oldLine : WZ1PaperIsLineClass oldData.coarse)
    (parent : Fin mesh.coarse.card) :
    wz2PaperCenteredLineTube (targetScale := rho)
        (mesh.coarse.tube parent) =
      mesh.coarse.tube parent := by
  let oldTube :=
    oldData.coarse.tube
      (mesh.representative (mesh.cellEquiv parent))
  change
    wz2PaperCenteredLineTube (targetScale := rho)
        (wz2PaperCenteredLineTube
          (targetScale := rho) oldTube) =
      wz2PaperCenteredLineTube
        (targetScale := rho) oldTube
  exact
    wz2PaperCenteredLineTube_recenter
      (middleScale := rho) (targetScale := rho)
      (tube := oldTube)
      (oldLine (mesh.representative (mesh.cellEquiv parent)))

theorem coarse_essentially_distinct
    (oldLine : WZ1PaperIsLineClass oldData.coarse)
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (oldData.coarse.tube first) =
          pureWZ2Prop62LineColor width stride
            (oldData.coarse.tube second))
    (separation :
      6 * rho <
        ((stride : ℝ) - 1) * width) :
    WZ1PaperIsEssentiallyDistinct mesh.coarse := by
  intro first second hne
  let firstCell := (mesh.cellEquiv first).1
  let secondCell := (mesh.cellEquiv second).1
  have firstCellMem : firstCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv first).2
  have secondCellMem : secondCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv second).2
  have firstRepresentative :=
    mesh.representative_mem firstCell firstCellMem
  have secondRepresentative :=
    mesh.representative_mem secondCell secondCellMem
  have cellNe : firstCell ≠ secondCell := by
    intro equality
    apply hne
    apply mesh.cellEquiv.injective
    exact Subtype.ext equality
  have colorEq :=
    sameColor
      (mesh.representative firstCell)
      (mesh.representative secondCell)
      firstRepresentative.1 secondRepresentative.1
  change
    rho <
      wz1PaperLineDistance
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (oldData.coarse.tube
            (mesh.representative firstCell)))
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (oldData.coarse.tube
            (mesh.representative secondCell)))
  rw [wz1PaperLineDistance_centeredLineTube_both
    (oldLine (mesh.representative firstCell))
    (oldLine (mesh.representative secondCell))]
  have separated :=
    pureWZ2_prop62_sameLineColor_distinctCell_separated
      widthPos
      (oldData.coarse.tube (mesh.representative firstCell))
      (oldData.coarse.tube (mesh.representative secondCell))
      (oldLine _) (oldLine _) colorEq <| by
        rw [firstRepresentative.2, secondRepresentative.2]
        exact cellNe
  linarith

theorem coarse_ordinary_essentially_distinct
    (oldLine : WZ1PaperIsLineClass oldData.coarse)
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (oldData.coarse.tube first) =
          pureWZ2Prop62LineColor width stride
            (oldData.coarse.tube second))
    (strongSeparation :
      360 * rho <
        ((stride : ℝ) - 1) * width) :
    WZ2PaperOrdinaryIsEssentiallyDistinct mesh.coarse := by
  intro first second distinct
  let firstCell := (mesh.cellEquiv first).1
  let secondCell := (mesh.cellEquiv second).1
  have firstCellMem : firstCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv first).2
  have secondCellMem : secondCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv second).2
  have firstRepresentative :=
    mesh.representative_mem firstCell firstCellMem
  have secondRepresentative :=
    mesh.representative_mem secondCell secondCellMem
  have cellNe : firstCell ≠ secondCell := by
    intro equality
    apply distinct
    apply mesh.cellEquiv.injective
    exact Subtype.ext equality
  have colorEq :=
    sameColor
      (mesh.representative firstCell)
      (mesh.representative secondCell)
      firstRepresentative.1 secondRepresentative.1
  have representativeSeparated :=
    pureWZ2_prop62_sameLineColor_distinctCell_separated
      widthPos
      (oldData.coarse.tube (mesh.representative firstCell))
      (oldData.coarse.tube (mesh.representative secondCell))
      (oldLine _) (oldLine _) colorEq <| by
        rw [firstRepresentative.2, secondRepresentative.2]
        exact cellNe
  have metricSeparated :
      60 * rho <
        wz1PaperLineDistance
          (mesh.coarse.tube first)
          (mesh.coarse.tube second) := by
    change
      60 * rho <
        wz1PaperLineDistance
          (wz2PaperCenteredLineTube
            (targetScale := rho)
            (oldData.coarse.tube
              (mesh.representative firstCell)))
          (wz2PaperCenteredLineTube
            (targetScale := rho)
            (oldData.coarse.tube
              (mesh.representative secondCell)))
    rw [wz1PaperLineDistance_centeredLineTube_both
      (oldLine _) (oldLine _)]
    linarith
  constructor
  · intro containment
    have close :=
      wz2_paper_bounded_centered_doubled_containment_lineDistance_le
        mesh.rho_pos mesh.rho_pos
        (mesh.coarse_line_class oldLine first)
        (mesh.coarse_line_class oldLine second)
        1
        (wz2PaperCenteredLineTube_midpoint_norm_le_one
          (oldLine
            (mesh.representative (mesh.cellEquiv first))))
        containment
    norm_num at close
    linarith
  · intro containment
    have close :=
      wz2_paper_bounded_centered_doubled_containment_lineDistance_le
        mesh.rho_pos mesh.rho_pos
        (mesh.coarse_line_class oldLine second)
        (mesh.coarse_line_class oldLine first)
        1
        (wz2PaperCenteredLineTube_midpoint_norm_le_one
          (oldLine
            (mesh.representative (mesh.cellEquiv second))))
        containment
    have symmetry :=
      wz1PaperLineDistance_symm
        (mesh.coarse.tube second) (mesh.coarse.tube first)
    norm_num at close
    rw [symmetry] at close
    linarith

noncomputable def toMetricPacketCoverInput
    (oldLine : WZ1PaperIsLineClass oldData.coarse)
    (fineLine : WZ1PaperIsLineClass mesh.complete.selectedFine.family)
    (fineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint
          (mesh.complete.selectedFine.family.tube source)‖ ≤ M)
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (oldData.coarse.tube first) =
          pureWZ2Prop62LineColor width stride
            (oldData.coarse.tube second))
    (separation :
      6 * rho <
        ((stride : ℝ) - 1) * width)
    (packetBound :
      (16 * M + 44) * scale + 6 * width ≤ rho / 2) :
    PureWZ2Prop62MetricPacketCoverInput
      (rho := rho) mesh.restrictedOldData M (6 * width) where
  fine_nonempty := by
    exact
      Fin.pos_iff_nonempty.mpr <|
        let parent :=
          Classical.choose mesh.selectedParents_nonempty
        let parentMem :=
          Classical.choose_spec mesh.selectedParents_nonempty
        let fiber :=
          oldData.cover.fullFiber_nonempty_of_uniform
            mesh.fine_nonempty oldData.full_fiber_uniform parent
        let ambientSource := Classical.choose fiber
        let ambientMem := Classical.choose_spec fiber
        have selectedMem :
            ambientSource ∈ mesh.complete.selectedFineIndices := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ ambientSource, by
              rw [(oldData.cover.mem_fullFiber_iff_parent_eq
                oldData.rho_pos.le parent ambientSource).mp ambientMem]
              exact parentMem⟩
        let selectedSource :=
          Classical.choose
            (mesh.complete.selectedFine_ambient_surjective
              ambientSource selectedMem)
        ⟨selectedSource⟩
  rho_pos := mesh.rho_pos
  fine_line_class := fineLine
  old_line_class := by
    exact oldLine.subfamily
      ((oldData.cover.hitParentSubfamily mesh.complete.selectedFine)
        |>.toTubeSubfamily)
  fine_midpoint_local := fineLocal
  coarse := mesh.coarse
  coarse_line_class := mesh.coarse_line_class oldLine
  coarse_essentially_distinct :=
    mesh.coarse_essentially_distinct
      oldLine widthPos stride sameColor separation
  packetParent := mesh.oldPacketParent
  packetParent_surjective := mesh.oldPacketParent_surjective
  parent_representative_close := fun parent =>
    mesh.oldPacketParent_representative_close
      parent oldLine widthPos
  packet_metric_bound := packetBound

end PureWZ2Prop62SelectedMeshCells

end Kakeya.Assouad

end
