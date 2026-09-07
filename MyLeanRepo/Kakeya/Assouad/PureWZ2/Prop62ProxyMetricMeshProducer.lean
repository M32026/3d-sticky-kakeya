import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CompleteParentScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62IndependentPureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking

/-!
# Proposition 6.2 proxy-axis metric mesh

The public Definition 2.12 parents determine complete strict packets but need
not belong to the WZ line chart.  This module keeps those packet indices and
uses a separate, same-index proxy axis only for the four-dimensional mesh.

All selected actual packets are retained whole.  Parents whose proxy axes lie
in the same mesh cell are merged, and the resulting metric fiber is exactly
the union of the corresponding complete actual packets.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62ProxySelectedMeshCells
    {delta scale proxyScale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    (proxyTube : Fin oldData.coarse.card → Kakeya.DeltaTube proxyScale)
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
            pureWZ2Prop62LineCell width (proxyTube parent))
          selectedParents,
      representative cell ∈ selectedParents ∧
        pureWZ2Prop62LineCell width
            (proxyTube (representative cell)) =
          cell

theorem exists_pureWZ2Prop62ProxySelectedMeshCells
    {delta scale proxyScale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    (proxyTube : Fin oldData.coarse.card → Kakeya.DeltaTube proxyScale)
    (width : ℝ)
    (rhoPos : 0 < rho)
    (fineNonempty : fine.Nonempty)
    (selectedParents : Finset (Fin oldData.coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty) :
    ∃ mesh :
        PureWZ2Prop62ProxySelectedMeshCells
          (rho := rho) oldData proxyTube width,
      mesh.selectedParents = selectedParents := by
  let occupiedCells : Finset (Fin 4 → ℤ) :=
    Finset.image
      (fun parent =>
        pureWZ2Prop62LineCell width (proxyTube parent))
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
  have chosen :=
    Classical.choose_spec (Finset.mem_image.mp hcell)
  change
    representative cell ∈ selectedParents ∧
      pureWZ2Prop62LineCell width
          (proxyTube (representative cell)) =
        cell
  rw [show representative cell =
      Classical.choose (Finset.mem_image.mp hcell) by
    simp only [representative, occupiedCells, dif_pos hcell]]
  exact chosen

namespace PureWZ2Prop62ProxySelectedMeshCells

variable
    {delta scale proxyScale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {proxyTube : Fin oldData.coarse.card → Kakeya.DeltaTube proxyScale}
    {width packetSpread : ℝ}
    (mesh :
      PureWZ2Prop62ProxySelectedMeshCells
        (rho := rho) oldData proxyTube width)

def occupiedCells : Finset (Fin 4 → ℤ) :=
  Finset.image
    (fun parent =>
      pureWZ2Prop62LineCell width (proxyTube parent))
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
      (proxyTube
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
  rw [oldData.cover.hitParent_ambient, sourceEq]
  exact
    (oldData.cover.mem_fullFiber_iff_parent_eq
      oldData.rho_pos.le ambientParent ambientSource).mp hsource

noncomputable def oldPacketParent
    (parent : Fin mesh.selectedOldCoarse.family.card) :
    Fin mesh.coarse.card :=
  mesh.cellEquiv.symm
    ⟨pureWZ2Prop62LineCell width
        (proxyTube (mesh.selectedOldCoarse.embedding parent)),
      Finset.mem_image.mpr
        ⟨mesh.selectedOldCoarse.embedding parent,
          mesh.selectedOldCoarse_parent_mem parent, rfl⟩⟩

@[simp] theorem oldPacketParent_cell
    (parent : Fin mesh.selectedOldCoarse.family.card) :
    mesh.cellEquiv (mesh.oldPacketParent parent) =
      ⟨pureWZ2Prop62LineCell width
          (proxyTube (mesh.selectedOldCoarse.embedding parent)),
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
        (proxyTube (mesh.selectedOldCoarse.embedding oldParent)) =
      (mesh.cellEquiv parent).1
  rw [holdParent, hcell]

theorem oldPacketParent_representative_close
    (proxyLine :
      ∀ parent, WZ1PaperTubeInLineClass (proxyTube parent))
    (widthPos : 0 < width)
    (parent : Fin mesh.selectedOldCoarse.family.card) :
    wz1PaperLineDistance
        (proxyTube (mesh.selectedOldCoarse.embedding parent))
        (mesh.coarse.tube (mesh.oldPacketParent parent)) ≤
      6 * width := by
  let cell :=
    pureWZ2Prop62LineCell width
      (proxyTube (mesh.selectedOldCoarse.embedding parent))
  have cellMem : cell ∈ mesh.occupiedCells :=
    Finset.mem_image.mpr
      ⟨mesh.selectedOldCoarse.embedding parent,
        mesh.selectedOldCoarse_parent_mem parent, rfl⟩
  have representativeData :=
    mesh.representative_mem cell cellMem
  change
    wz1PaperLineDistance
        (proxyTube (mesh.selectedOldCoarse.embedding parent))
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (proxyTube
            (mesh.representative
              (mesh.cellEquiv (mesh.oldPacketParent parent))))) ≤
      6 * width
  rw [wz1PaperLineDistance_centeredLineTube_right
    (proxyLine (mesh.selectedOldCoarse.embedding parent))
    (proxyLine
      (mesh.representative
        (mesh.cellEquiv (mesh.oldPacketParent parent))))]
  apply pureWZ2_prop62_sameLineCell_lineDistance_le
    widthPos _ _ (proxyLine _) (proxyLine _)
  rw [mesh.oldPacketParent_cell]
  exact representativeData.2.symm

theorem coarse_line_class
    (proxyLine :
      ∀ parent, WZ1PaperTubeInLineClass (proxyTube parent)) :
    WZ1PaperIsLineClass mesh.coarse := by
  intro parent
  exact
    wz2PaperCenteredLineTube_lineClass
      (proxyLine
        (mesh.representative (mesh.cellEquiv parent)))

theorem coarse_essentially_distinct
    (proxyLine :
      ∀ parent, WZ1PaperTubeInLineClass (proxyTube parent))
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (proxyTube first) =
          pureWZ2Prop62LineColor width stride
            (proxyTube second))
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
          (proxyTube (mesh.representative firstCell)))
        (wz2PaperCenteredLineTube
          (targetScale := rho)
          (proxyTube (mesh.representative secondCell)))
  rw [wz1PaperLineDistance_centeredLineTube_both
    (proxyLine (mesh.representative firstCell))
    (proxyLine (mesh.representative secondCell))]
  have separated :=
    pureWZ2_prop62_sameLineColor_distinctCell_separated
      widthPos
      (proxyTube (mesh.representative firstCell))
      (proxyTube (mesh.representative secondCell))
      (proxyLine _) (proxyLine _) colorEq <| by
        rw [firstRepresentative.2, secondRepresentative.2]
        exact cellNe
  linarith

noncomputable def toProxyMetricPacketCoverInput
    (fineLine :
      WZ1PaperIsLineClass mesh.complete.selectedFine.family)
    (proxyLine :
      ∀ parent, WZ1PaperTubeInLineClass (proxyTube parent))
    (packetProxyClose :
      ∀ parent source,
        source ∈
            wz2PaperOrdinaryFullFiberIndices
              fine oldData.coarse parent →
          wz1PaperLineDistance
              (fine.tube source) (proxyTube parent) ≤
            packetSpread)
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (proxyTube first) =
          pureWZ2Prop62LineColor width stride
            (proxyTube second))
    (separation :
      6 * rho <
        ((stride : ℝ) - 1) * width)
    (packetBound :
      packetSpread + 6 * width ≤ rho / 2) :
    PureWZ2Prop62ProxyMetricPacketCoverInput
      (rho := rho) mesh.restrictedOldData
      (packetSpread + 6 * width) where
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
  coarse := mesh.coarse
  coarse_line_class := mesh.coarse_line_class proxyLine
  coarse_essentially_distinct :=
    mesh.coarse_essentially_distinct
      proxyLine widthPos stride sameColor separation
  packetParent := mesh.oldPacketParent
  packetParent_surjective := mesh.oldPacketParent_surjective
  packet_proxy_close := by
    intro parent source hsource
    let ambientParent :=
      mesh.selectedOldCoarse.embedding parent
    let ambientSource :=
      mesh.complete.selectedFine.embedding source
    have sourceAmbient :
        ambientSource ∈
          wz2PaperOrdinaryFullFiberIndices
            fine oldData.coarse ambientParent := by
      have restrictedParent :
          mesh.restrictedOldData.cover.parent source = parent :=
        (mesh.restrictedOldData.cover.mem_fullFiber_iff_parent_eq
          mesh.restrictedOldData.rho_pos.le parent source).mp hsource
      have ambientParentEq :
          oldData.cover.parent ambientSource = ambientParent := by
        calc
          oldData.cover.parent ambientSource =
              mesh.selectedOldCoarse.embedding
                (mesh.restrictedOldData.cover.parent source) := by
            exact
              (mesh.restrictedOldData_parent_ambient source).symm
          _ = mesh.selectedOldCoarse.embedding parent := by
            rw [restrictedParent]
          _ = ambientParent := rfl
      exact
        (oldData.cover.mem_fullFiber_iff_parent_eq
          oldData.rho_pos.le ambientParent ambientSource).mpr
          ambientParentEq
    rw [mesh.complete.selectedFine.tube_eq]
    exact
      (wz1PaperLineDistance_triangle
        (fine.tube ambientSource)
        (proxyTube ambientParent)
        (mesh.coarse.tube (mesh.oldPacketParent parent))).trans <| by
          gcongr
          · exact packetProxyClose ambientParent ambientSource sourceAmbient
          · exact
              mesh.oldPacketParent_representative_close
                proxyLine widthPos parent
  packet_metric_bound := packetBound

end PureWZ2Prop62ProxySelectedMeshCells

namespace PureWZ2Prop62LaminarPureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)

/-- The canonical Section 6 proxy axis attached to one actual parent. -/
noncomputable def coordinateProxyTube
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    Kakeya.DeltaTube (schedule.actualScale coordinate) :=
  (schedule.representativeLineFamily
    fineNonempty coordinate
    (schedule.actualScale coordinate)).tube parent

theorem coordinateProxyTube_lineClass
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    WZ1PaperTubeInLineClass
      (schedule.coordinateProxyTube
        fineNonempty coordinate parent) :=
  schedule.representativeLineFamily_lineClass
    fineNonempty fineLine coordinate
    (schedule.actualScale coordinate) parent

/--
Every member of one actual complete packet lies in the prescribed line ball
about its canonical proxy axis.
-/
theorem completePacket_coordinateProxyTube_lineDistance_le
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card)
    (source : Fin fine.card)
    (sourceMem :
      source ∈
        wz2PaperOrdinaryFullFiberIndices
          fine (schedule.scaleData coordinate).coarse parent) :
    wz1PaperLineDistance
        (fine.tube source)
        (schedule.coordinateProxyTube
          fineNonempty coordinate parent) ≤
      600000 * schedule.actualScale coordinate := by
  have sourceContainment :
      (fine.tube source).carrier ⊆
        ((schedule.scaleData coordinate).coarse.tube parent).carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent source).mp sourceMem
  have representativeContainment :
      (fine.tube
        (schedule.parentRepresentative
          fineNonempty coordinate parent)).carrier ⊆
        ((schedule.scaleData coordinate).coarse.tube parent).carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent
      (schedule.parentRepresentative
        fineNonempty coordinate parent)).mp
      (schedule.parentRepresentative_mem
        fineNonempty coordinate parent)
  change
    wz1PaperLineDistance
        (fine.tube source)
        (wz2PaperRelabelTube
          (targetScale := schedule.actualScale coordinate)
          (wz2PaperCanonicalLineTube
            (fine.tube
              (schedule.parentRepresentative
                fineNonempty coordinate parent)))) ≤
      600000 * schedule.actualScale coordinate
  rw [wz2PaperRelabelTube_lineDistance_right]
  have canonicalDistance :
      wz1PaperLineDistance
          (fine.tube source)
          (wz2PaperCanonicalLineTube
            (fine.tube
              (schedule.parentRepresentative
                fineNonempty coordinate parent))) =
        wz1PaperLineDistance
          (fine.tube source)
          (fine.tube
            (schedule.parentRepresentative
              fineNonempty coordinate parent)) := by
    unfold wz1PaperLineDistance
    rw [
      wz2PaperCanonicalLineTube_axisZero
        (fineLine
          (schedule.parentRepresentative
            fineNonempty coordinate parent)),
      wz2PaperCanonicalLineTube_paperDirection
        (fineLine
          (schedule.parentRepresentative
            fineNonempty coordinate parent))
    ]
  rw [canonicalDistance]
  by_cases actualSmall :
      schedule.actualScale coordinate ≤ 1 / 10000
  · exact
      wz1PaperLineDistance_le_of_common_actual_parent
        (schedule.scaleData coordinate).delta_pos
        (schedule.delta_le_actualScale coordinate)
        actualSmall
        (fineLine source)
        (fineLine
          (schedule.parentRepresentative
            fineNonempty coordinate parent))
        (fineBase source)
        (fineBase
          (schedule.parentRepresentative
            fineNonempty coordinate parent))
        sourceContainment representativeContainment
  · have sourceZero :
        ‖wz1TubeAxisZeroPoint (fine.tube source)‖ ≤ 1 :=
      pureWZ2_axisZero_norm_le_one (fineLine source)
    have representativeZero :
        ‖wz1TubeAxisZeroPoint
            (fine.tube
              (schedule.parentRepresentative
                fineNonempty coordinate parent))‖ ≤
          1 :=
      pureWZ2_axisZero_norm_le_one <|
        fineLine
          (schedule.parentRepresentative
            fineNonempty coordinate parent)
    have zeroDistance :
        dist
            (wz1TubeAxisZeroPoint (fine.tube source))
            (wz1TubeAxisZeroPoint
              (fine.tube
                (schedule.parentRepresentative
                  fineNonempty coordinate parent))) ≤
          2 := by
      rw [dist_eq_norm]
      exact
        (norm_sub_le _ _).trans <| by
          linarith
    have angleBound :
        InnerProductGeometry.angle
            (wz1PaperDirection (fine.tube source))
            (wz1PaperDirection
              (fine.tube
                (schedule.parentRepresentative
                  fineNonempty coordinate parent))) ≤
          Real.pi :=
      InnerProductGeometry.angle_le_pi _ _
    unfold wz1PaperLineDistance
    have actualLarge :
        1 / 10000 <
          schedule.actualScale coordinate :=
      lt_of_not_ge actualSmall
    nlinarith [Real.pi_lt_four]

/-- Select proxy-axis mesh representatives for any nonempty actual-parent set. -/
theorem exists_coordinateProxySelectedMeshCells
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (rho width : ℝ)
    (rhoPos : 0 < rho)
    (selectedParents :
      Finset (Fin (schedule.scaleData coordinate).coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty) :
    ∃ mesh :
        PureWZ2Prop62ProxySelectedMeshCells
          (rho := rho)
          (schedule.scaleData coordinate)
          (schedule.coordinateProxyTube
            fineNonempty coordinate)
          width,
      mesh.selectedParents = selectedParents :=
  exists_pureWZ2Prop62ProxySelectedMeshCells
    (schedule.scaleData coordinate)
    (schedule.coordinateProxyTube fineNonempty coordinate)
    width rhoPos fineNonempty
    selectedParents selectedParentsNonempty

end PureWZ2Prop62LaminarPureSchedule

namespace PureWZ2Prop62ProxySelectedMeshCells

/--
Specialize the proxy mesh to one coordinate of the literal Lemma 2.13 tree.
The output keeps the restricted actual scale data for packet CWA while all
Section 6 geometry is carried by the representative axes.
-/
noncomputable def toLaminarScheduleMetricPacketCoverInput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (coordinate : Fin schedule.levelCount)
    {width : ℝ}
    (mesh :
      PureWZ2Prop62ProxySelectedMeshCells
        (rho := rho)
        (schedule.scaleData coordinate)
        (schedule.coordinateProxyTube
          fineNonempty coordinate)
        width)
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (schedule.coordinateProxyTube
              fineNonempty coordinate first) =
          pureWZ2Prop62LineColor width stride
            (schedule.coordinateProxyTube
              fineNonempty coordinate second))
    (separation :
      6 * rho < ((stride : ℝ) - 1) * width)
    (packetBound :
      600000 * schedule.actualScale coordinate +
          6 * width ≤
        rho / 2) :
    PureWZ2Prop62ProxyMetricPacketCoverInput
      (rho := rho) mesh.restrictedOldData
      (600000 * schedule.actualScale coordinate +
        6 * width) := by
  have selectedFineLine :
      WZ1PaperIsLineClass mesh.complete.selectedFine.family :=
    fineLine.subfamily mesh.complete.selectedFine.toTubeSubfamily
  exact
    mesh.toProxyMetricPacketCoverInput
      selectedFineLine
      (schedule.coordinateProxyTube_lineClass
        fineNonempty fineLine coordinate)
      (schedule.completePacket_coordinateProxyTube_lineDistance_le
        fineNonempty fineLine fineBase coordinate)
      widthPos stride sameColor separation packetBound

end PureWZ2Prop62ProxySelectedMeshCells

end Kakeya.Assouad

end
