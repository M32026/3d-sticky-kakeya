import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRepresentativeMiddle
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SaturatedScaleRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricFiberRequestedRoute
import Mathlib.Tactic

/-!
# Proposition 6.2 metric-parent V4 lower route

This module packages the exact final metric fibers from the unique quotient
cleanup into the requested-scale lower route.  The analytic descendants use the
public laminar schedule and the same metric core.  Their representative-middle
replacement is supplied by the all-scale pre-core coloring.

All scalar inequalities remain explicit inputs.  In particular this module
does not choose a second family, run a second cleanup, or assume a completed
fiber CWA.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem laminar_nodeAt_coordinate_eq_fullFiber
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount)
    (leaf : Fin fine.card) :
    schedule.nodeAt (coordinate.1 + 1) leaf =
      wz2PaperOrdinaryFullFiberIndices
        fine
        (schedule.scaleData coordinate).coarse
        ((schedule.scaleData coordinate).cover.parent leaf) := by
  rw [schedule.nodeAt_succ coordinate.2]
  ext source
  rw [
    (schedule.scaleData coordinate).cover.mem_fullFiber_iff_parent_eq
      (schedule.scaleData coordinate).rho_pos.le
  ]
  simp

private theorem laminar_tree_fiber_coordinate_nodeAt_eq_fullFiber
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount)
    (leaf : Fin fine.card) :
    schedule.tree.fiber
        (coordinate.1 + 1)
        (schedule.nodeAt (coordinate.1 + 1) leaf) =
      wz2PaperOrdinaryFullFiberIndices
        fine
        (schedule.scaleData coordinate).coarse
        ((schedule.scaleData coordinate).cover.parent leaf) := by
  ext source
  constructor
  · intro sourceMem
    have nodeEq :
        schedule.nodeAt (coordinate.1 + 1) source =
          schedule.nodeAt (coordinate.1 + 1) leaf :=
      (Finset.mem_filter.mp sourceMem).2
    have sourceOwn :
        source ∈
          wz2PaperOrdinaryFullFiberIndices
            fine
            (schedule.scaleData coordinate).coarse
            ((schedule.scaleData coordinate).cover.parent source) :=
      (schedule.scaleData coordinate).cover.parent_mem_fullFiber source
    rw [
      ← laminar_nodeAt_coordinate_eq_fullFiber schedule coordinate source,
      nodeEq,
      laminar_nodeAt_coordinate_eq_fullFiber schedule coordinate leaf
    ] at sourceOwn
    exact sourceOwn
  · intro sourceMem
    have parentEq :
        (schedule.scaleData coordinate).cover.parent source =
          (schedule.scaleData coordinate).cover.parent leaf :=
      ((schedule.scaleData coordinate).cover.mem_fullFiber_iff_parent_eq
        (schedule.scaleData coordinate).rho_pos.le
        ((schedule.scaleData coordinate).cover.parent leaf)
        source).mp sourceMem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    change
      schedule.nodeAt (coordinate.1 + 1) source =
      schedule.nodeAt (coordinate.1 + 1) leaf
    rw [
      laminar_nodeAt_coordinate_eq_fullFiber schedule coordinate source,
      laminar_nodeAt_coordinate_eq_fullFiber schedule coordinate leaf,
      parentEq
    ]

private theorem laminar_selectedFullFiber_count_le_of_core_density
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount)
    (densityConstant : ℕ)
    {selected core : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (coreSubset : core ⊆ selected)
    (nodeDensity :
      ∀ node : Finset (Fin fine.card),
        (core ∩
          schedule.tree.fiber
            (coordinate.1 + 1) node).Nonempty →
          selected.card *
              (schedule.tree.fiber
                (coordinate.1 + 1) node).card ≤
            densityConstant *
              (core ∩
                schedule.tree.fiber
                  (coordinate.1 + 1) node).card *
              fine.card)
    (parent :
      Fin
        ((schedule.scaleData coordinate).cover.hitParentSubfamily
          (WZ2PaperPureTubeSubfamily.fromFinset fine core)).family.card) :
    wz2PaperOrdinaryFullFiberCount
        fine
        (schedule.scaleData coordinate).coarse
        (((schedule.scaleData coordinate).cover.hitParentSubfamily
          (WZ2PaperPureTubeSubfamily.fromFinset fine core)).embedding
            parent) ≤
      ((densityConstant : ENNReal) *
          fine.enncard *
          (selected.card : ENNReal)⁻¹) *
        wz2PaperOrdinaryFullFiberCount
          (WZ2PaperPureTubeSubfamily.fromFinset fine core).family
          ((schedule.scaleData coordinate).cover.hitParentSubfamily
            (WZ2PaperPureTubeSubfamily.fromFinset fine core)).family
          parent := by
  let coreFine :=
    WZ2PaperPureTubeSubfamily.fromFinset fine core
  let coreCoarse :=
    (schedule.scaleData coordinate).cover.hitParentSubfamily coreFine
  rcases
      (schedule.scaleData coordinate).cover.hitParent_surjective
        coreFine parent
    with ⟨source, sourceParent⟩
  let leaf := coreFine.embedding source
  have leafCore : leaf ∈ core :=
    Finset.orderEmbOfFin_mem core rfl source
  have leafFiber :
      leaf ∈
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ leaf, rfl⟩
  have coreFiberNonempty :
      (core ∩
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).Nonempty :=
    ⟨leaf, Finset.mem_inter.mpr ⟨leafCore, leafFiber⟩⟩
  have densityNat :=
    nodeDensity
      (schedule.nodeAt (coordinate.1 + 1) leaf)
      coreFiberNonempty
  have densityENN :
      (selected.card : ENNReal) *
          ((schedule.tree.fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (densityConstant : ENNReal) *
          ((core ∩
            schedule.tree.fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          fine.enncard := by
    change
      (selected.card : ENNReal) *
          ((schedule.tree.fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
            ENNReal) ≤
        (densityConstant : ENNReal) *
          ((core ∩
            schedule.tree.fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) *
          (fine.card : ENNReal)
    exact_mod_cast densityNat
  have selectedPos : 0 < (selected.card : ENNReal) := by
    exact_mod_cast selectedNonempty.card_pos
  have selectedFinite : (selected.card : ENNReal) ≠ ⊤ := by
    simp
  have fiberBound :
      ((schedule.tree.fiber
        (coordinate.1 + 1)
        (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
        ENNReal) ≤
        ((densityConstant : ENNReal) *
            fine.enncard *
            (selected.card : ENNReal)⁻¹) *
          ((core ∩
            schedule.tree.fiber
              (coordinate.1 + 1)
              (schedule.nodeAt
                (coordinate.1 + 1) leaf)).card : ENNReal) := by
    calc
      ((schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).card :
          ENNReal) =
          ((selected.card : ENNReal) *
            (selected.card : ENNReal)⁻¹) *
              ((schedule.tree.fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        rw [ENNReal.mul_inv_cancel selectedPos.ne' selectedFinite]
        simp
      _ =
          ((selected.card : ENNReal) *
              ((schedule.tree.fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal)) *
            (selected.card : ENNReal)⁻¹ := by
        ring
      _ ≤
          ((densityConstant : ENNReal) *
              ((core ∩
                schedule.tree.fiber
                  (coordinate.1 + 1)
                  (schedule.nodeAt
                    (coordinate.1 + 1) leaf)).card : ENNReal) *
              fine.enncard) *
            (selected.card : ENNReal)⁻¹ := by
        gcongr
      _ =
          ((densityConstant : ENNReal) *
              fine.enncard *
              (selected.card : ENNReal)⁻¹) *
            ((core ∩
              schedule.tree.fiber
                (coordinate.1 + 1)
                (schedule.nodeAt
                  (coordinate.1 + 1) leaf)).card : ENNReal) := by
        ring
  have parentEq :
      (schedule.scaleData coordinate).cover.parent leaf =
        coreCoarse.embedding parent := by
    change
      (schedule.scaleData coordinate).cover.parent
          (coreFine.embedding source) =
        coreCoarse.embedding parent
    rw [←
      (schedule.scaleData coordinate).cover.hitParent_ambient
        coreFine source, sourceParent]
  have coreFiberCard :
      (wz2PaperOrdinaryFullFiberIndices
          coreFine.family coreCoarse.family parent).card =
        (core ∩
          schedule.tree.fiber
            (coordinate.1 + 1)
            (schedule.nodeAt (coordinate.1 + 1) leaf)).card := by
    rw [wz2_paper_selected_fullFiber_card]
    change
      (wz2PaperSelectedAmbientFullFiberIndices
        coreFine (coreCoarse.embedding parent)).card =
      (core ∩
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).card
    congr 1
    ext ambientSource
    simp only [
      wz2PaperSelectedAmbientFullFiberIndices,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter
    ]
    have imageEq :
        Finset.image coreFine.embedding Finset.univ = core := by
      ext index
      constructor
      · intro indexMem
        rcases Finset.mem_image.mp indexMem with ⟨target, _targetUniv, rfl⟩
        exact Finset.orderEmbOfFin_mem core rfl target
      · intro indexMem
        let equivalence : Fin core.card ≃ core :=
          (core.orderIsoOfFin rfl).toEquiv
        exact
          Finset.mem_image.mpr
            ⟨equivalence.symm ⟨index, indexMem⟩,
              Finset.mem_univ _,
              congrArg Subtype.val
                (equivalence.apply_symm_apply
                  ⟨index, indexMem⟩)⟩
    rw [imageEq, ← parentEq]
    rw [laminar_tree_fiber_coordinate_nodeAt_eq_fullFiber
      schedule coordinate leaf]
  rw [
    wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount,
    ← parentEq,
    ← laminar_tree_fiber_coordinate_nodeAt_eq_fullFiber
      schedule coordinate leaf,
    coreFiberCard
  ]
  exact fiberBound

namespace PureWZ2Prop62LaminarPureSchedule

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    (packetCoordinate : Fin schedule.levelCount)
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)

/-- The ambient fine family selected by the unique quotient cleanup receipt. -/
private noncomputable def lowerRouteAmbientCoreFine :
    WZ2PaperPureTubeSubfamily fine :=
  WZ2PaperPureTubeSubfamily.fromFinset
    fine metricCore.cleanup.core.core

/-- Below the inserted metric level, the auxiliary tree is the laminar tree. -/
private theorem lowerRoute_descendant_tree_fiber_eq
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val)
    (node : Finset (Fin fine.card)) :
    metricCore.cleanup.auxiliary.tree.fiber
        (coordinate.1 + 2) node =
      schedule.tree.fiber (coordinate.1 + 1) node := by
  ext leaf
  simp only [PureWZ2Prop62FiniteTree.fiber,
    Finset.mem_filter, Finset.mem_univ, true_and]
  change
    metricCore.cleanup.auxiliary.nodeAt
        (coordinate.1 + 2) leaf = node ↔
      schedule.nodeAt (coordinate.1 + 1) leaf = node
  have afterAuxiliary :
      packetCoordinate.1 + 1 < coordinate.1 + 2 := by
    omega
  rw [metricCore.cleanup.auxiliary.nodeAt_fine afterAuxiliary]
  have levelEq : coordinate.1 + 2 - 1 = coordinate.1 + 1 := by
    omega
  rw [levelEq]

/-- The same cleanup receipt supplies density at every descendant old level. -/
private theorem lowerRoute_descendant_old_node_density
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val)
    (node : Finset (Fin fine.card))
    (nonempty :
      (metricCore.cleanup.core.core ∩
        schedule.tree.fiber (coordinate.1 + 1) node).Nonempty) :
    metricCore.cleanup.preliminary.card *
          (schedule.tree.fiber (coordinate.1 + 1) node).card ≤
      2 ^ (schedule.levelCount + 1) *
        (metricCore.cleanup.core.core ∩
          schedule.tree.fiber (coordinate.1 + 1) node).card *
        fine.card := by
  have fiberEq :=
    schedule.lowerRoute_descendant_tree_fiber_eq
      packetCoordinate metricCore coordinate coordinateAfter node
  have liftedNonempty :
      (metricCore.cleanup.core.core ∩
        metricCore.cleanup.auxiliary.tree.fiber
          (coordinate.1 + 2) node).Nonempty := by
    rwa [fiberEq]
  have density :=
    metricCore.cleanup.core.node_density
      (coordinate.1 + 2)
      (by omega : coordinate.1 + 2 ≤ schedule.levelCount + 1)
      node liftedNonempty
  simpa only [fiberEq, Fintype.card_fin] using density

/--
Restrict one public old-scale witness to the unique ambient cleanup core.
The only changed CWA constant is the receipt's density ratio.
-/
private noncomputable def lowerRouteAmbientCoreScaleData
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val) :
    WZ2PaperPureScaleCoverData
      (schedule.lowerRouteAmbientCoreFine
        (packetCoordinate := packetCoordinate) metricCore).family
      (schedule.actualScale coordinate)
      (ambientConstant * metricCore.quotientDensityLoss) := by
  let coreFine :=
    schedule.lowerRouteAmbientCoreFine
      (packetCoordinate := packetCoordinate) metricCore
  let coreCoarse :=
    (schedule.scaleData coordinate).cover.hitParentSubfamily coreFine
  let coreCover :=
    (schedule.scaleData coordinate).cover.restrictToHitParents coreFine
  have coreUniform :
      WZ2PaperPureFullFibersAreCUniform
        coreFine.family coreCoarse.family
        (ambientConstant * metricCore.quotientDensityLoss) := by
    intro first second
    change
      wz2PaperOrdinaryFullFiberCount
          (WZ2PaperPureTubeSubfamily.fromFinset
            fine metricCore.cleanup.core.core).family
          ((schedule.scaleData coordinate).cover.hitParentSubfamily
            (WZ2PaperPureTubeSubfamily.fromFinset
              fine metricCore.cleanup.core.core)).family
          first ≤
        (ambientConstant * metricCore.quotientDensityLoss) *
          wz2PaperOrdinaryFullFiberCount
            (WZ2PaperPureTubeSubfamily.fromFinset
              fine metricCore.cleanup.core.core).family
            ((schedule.scaleData coordinate).cover.hitParentSubfamily
              (WZ2PaperPureTubeSubfamily.fromFinset
                fine metricCore.cleanup.core.core)).family
            second
    calc
      wz2PaperOrdinaryFullFiberCount
          (WZ2PaperPureTubeSubfamily.fromFinset
            fine metricCore.cleanup.core.core).family
          ((schedule.scaleData coordinate).cover.hitParentSubfamily
            (WZ2PaperPureTubeSubfamily.fromFinset
              fine metricCore.cleanup.core.core)).family
          first ≤
        wz2PaperOrdinaryFullFiberCount
          fine (schedule.scaleData coordinate).coarse
          (((schedule.scaleData coordinate).cover.hitParentSubfamily
            (WZ2PaperPureTubeSubfamily.fromFinset
              fine metricCore.cleanup.core.core)).embedding first) := by
        rw [wz2PaperOrdinaryFullFiberCount,
          wz2PaperOrdinaryFullFiberCount,
          wz2_paper_selected_fullFiber_card]
        exact_mod_cast
          Finset.card_le_card <| by
            intro source sourceMem
            exact (Finset.mem_filter.mp sourceMem).2.2
      _ ≤
        ambientConstant *
          wz2PaperOrdinaryFullFiberCount
            fine (schedule.scaleData coordinate).coarse
            (((schedule.scaleData coordinate).cover.hitParentSubfamily
              (WZ2PaperPureTubeSubfamily.fromFinset
                fine metricCore.cleanup.core.core)).embedding second) :=
        (schedule.scaleData coordinate).full_fiber_uniform _ _
      _ ≤
        ambientConstant *
          (metricCore.quotientDensityLoss *
            wz2PaperOrdinaryFullFiberCount
              (WZ2PaperPureTubeSubfamily.fromFinset
                fine metricCore.cleanup.core.core).family
              ((schedule.scaleData coordinate).cover.hitParentSubfamily
                (WZ2PaperPureTubeSubfamily.fromFinset
                  fine metricCore.cleanup.core.core)).family
              second) := by
        gcongr
        exact
          (by
            simpa only [
              PureWZ2Prop62ProxyQuotientMetricCoreOutput.quotientDensityLoss,
              Nat.cast_pow, Nat.cast_ofNat
            ] using
              laminar_selectedFullFiber_count_le_of_core_density
                schedule coordinate (2 ^ (schedule.levelCount + 1))
                metricCore.cleanup.preliminary_nonempty
                metricCore.cleanup.core.core_subset
                (fun node nodeNonempty =>
                  schedule.lowerRoute_descendant_old_node_density
                    packetCoordinate metricCore coordinate coordinateAfter
                    node nodeNonempty)
                second)
      _ =
        (ambientConstant * metricCore.quotientDensityLoss) *
          wz2PaperOrdinaryFullFiberCount
            (WZ2PaperPureTubeSubfamily.fromFinset
              fine metricCore.cleanup.core.core).family
            ((schedule.scaleData coordinate).cover.hitParentSubfamily
              (WZ2PaperPureTubeSubfamily.fromFinset
                fine metricCore.cleanup.core.core)).family
            second := by
        ring
  let restricted :=
    (schedule.scaleData coordinate).restrict
      coreFine coreCoarse coreCover coreUniform
      (fun parent =>
        laminar_selectedFullFiber_count_le_of_core_density
          schedule coordinate (2 ^ (schedule.levelCount + 1))
          metricCore.cleanup.preliminary_nonempty
          metricCore.cleanup.core.core_subset
          (fun node nodeNonempty =>
            schedule.lowerRoute_descendant_old_node_density
              packetCoordinate metricCore coordinate coordinateAfter
              node nodeNonempty)
          parent)
  have constantLe :
      max
          (ambientConstant * metricCore.quotientDensityLoss)
          (((2 ^ (schedule.levelCount + 1) : ℕ) : ENNReal) *
            fine.enncard *
            (metricCore.cleanup.preliminary.card : ENNReal)⁻¹ *
            ambientConstant) ≤
        ambientConstant * metricCore.quotientDensityLoss := by
    simp only [
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.quotientDensityLoss,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [show
      (2 : ENNReal) ^ (schedule.levelCount + 1) *
              fine.enncard *
              (metricCore.cleanup.preliminary.card : ENNReal)⁻¹ *
              ambientConstant =
          ambientConstant *
            ((2 : ENNReal) ^ (schedule.levelCount + 1) *
              fine.enncard *
              (metricCore.cleanup.preliminary.card : ENNReal)⁻¹) by ring,
      max_self]
  exact restricted.mono constantLe

/-- Reindexing between the final Section 6 family and the ambient cleanup core. -/
private noncomputable def lowerRouteFinalToAmbientCoreEquiv :
    Fin metricCore.restriction.fineSelected.family.card ≃
      Fin
        (schedule.lowerRouteAmbientCoreFine
          (packetCoordinate := packetCoordinate) metricCore).family.card :=
  Equiv.ofBijective
    (fun source =>
      ((metricCore.cleanup.core.core.orderIsoOfFin rfl).symm
        ⟨metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding source),
          by
            have selectedMem :
                metricCore.restriction.fineSelected.embedding source ∈
                  metricCore.pulledBack := by
              have imageMem :
                  metricCore.restriction.fineSelected.embedding source ∈
                    Finset.image
                      metricCore.restriction.fineSelected.embedding
                      Finset.univ :=
                Finset.mem_image.mpr
                  ⟨source, Finset.mem_univ source, rfl⟩
              simpa only [metricCore.restriction.fine_image_univ] using
                imageMem
            rw [← metricCore.ambientCore_eq, ← metricCore.image_eq]
            exact Finset.mem_image.mpr
              ⟨metricCore.restriction.fineSelected.embedding source,
                selectedMem, rfl⟩⟩))
    ⟨by
      intro first second indexEq
      apply metricCore.restriction.fineSelected.embedding.injective
      apply metricCore.metric.mesh.complete.selectedFine.embedding.injective
      have valueEq := congrArg Subtype.val <|
        congrArg
          (metricCore.cleanup.core.core.orderIsoOfFin rfl)
          indexEq
      simpa using valueEq,
     by
      intro coreSource
      have coreMem :
          (schedule.lowerRouteAmbientCoreFine
            (packetCoordinate := packetCoordinate) metricCore).embedding
              coreSource ∈
            metricCore.cleanup.core.core :=
        Finset.orderEmbOfFin_mem _ rfl coreSource
      have ambientMem :
          (schedule.lowerRouteAmbientCoreFine
            (packetCoordinate := packetCoordinate) metricCore).embedding
              coreSource ∈
            metricCore.ambientCore := by
        rwa [metricCore.ambientCore_eq]
      have imageMem :
          (schedule.lowerRouteAmbientCoreFine
            (packetCoordinate := packetCoordinate) metricCore).embedding
              coreSource ∈
            Finset.image
              metricCore.metric.mesh.complete.selectedFine.embedding
              metricCore.pulledBack := by
        rwa [metricCore.image_eq]
      rcases Finset.mem_image.mp imageMem with
        ⟨selectedSource, selectedMem, selectedEq⟩
      have finalImage :
          selectedSource ∈
            Finset.image metricCore.restriction.fineSelected.embedding
              Finset.univ := by
        rwa [metricCore.restriction.fine_image_univ]
      rcases Finset.mem_image.mp finalImage with
        ⟨source, _sourceMem, sourceEq⟩
      refine ⟨source, ?_⟩
      apply
        ((metricCore.cleanup.core.core.orderIsoOfFin rfl).symm_apply_eq).2
      apply Subtype.ext
      change
        metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding source) =
          (schedule.lowerRouteAmbientCoreFine
            (packetCoordinate := packetCoordinate) metricCore).embedding
              coreSource
      rw [sourceEq]
      exact selectedEq⟩

private theorem lowerRouteFinalToAmbientCoreEquiv_embedding
    (source : Fin metricCore.restriction.fineSelected.family.card) :
    (schedule.lowerRouteAmbientCoreFine
      (packetCoordinate := packetCoordinate) metricCore).embedding
        (schedule.lowerRouteFinalToAmbientCoreEquiv
          packetCoordinate metricCore source) =
      metricCore.metric.mesh.complete.selectedFine.embedding
        (metricCore.restriction.fineSelected.embedding source) := by
  unfold lowerRouteFinalToAmbientCoreEquiv lowerRouteAmbientCoreFine
  change
    metricCore.cleanup.core.core.orderEmbOfFin rfl
        ((metricCore.cleanup.core.core.orderIsoOfFin rfl).symm
          ⟨metricCore.metric.mesh.complete.selectedFine.embedding
              (metricCore.restriction.fineSelected.embedding source), _⟩) =
      metricCore.metric.mesh.complete.selectedFine.embedding
        (metricCore.restriction.fineSelected.embedding source)
  exact congrArg Subtype.val <|
    (metricCore.cleanup.core.core.orderIsoOfFin rfl).apply_symm_apply _

private theorem lowerRouteFinalToAmbientCoreEquiv_tube
    (source : Fin metricCore.restriction.fineSelected.family.card) :
    metricCore.restriction.fineSelected.family.tube source =
      (schedule.lowerRouteAmbientCoreFine
        (packetCoordinate := packetCoordinate) metricCore).family.tube
        (schedule.lowerRouteFinalToAmbientCoreEquiv
          packetCoordinate metricCore source) := by
  rw [metricCore.restriction.fineSelected.tube_eq,
    metricCore.metric.mesh.complete.selectedFine.tube_eq,
    (schedule.lowerRouteAmbientCoreFine
      (packetCoordinate := packetCoordinate) metricCore).tube_eq,
    schedule.lowerRouteFinalToAmbientCoreEquiv_embedding
      packetCoordinate metricCore]

/-- The unique-core old witness reindexed onto the final Section 6 family. -/
private noncomputable def lowerRouteFinalCoreScaleData
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val) :
    WZ2PaperPureScaleCoverData
      metricCore.restriction.fineSelected.family
      (schedule.actualScale coordinate)
      (ambientConstant * metricCore.quotientDensityLoss) :=
  (lowerRouteAmbientCoreScaleData
      schedule packetCoordinate metricCore coordinate coordinateAfter).reindex
    (schedule.lowerRouteFinalToAmbientCoreEquiv packetCoordinate metricCore)
    (schedule.lowerRouteFinalToAmbientCoreEquiv_tube
      packetCoordinate metricCore)

/-- Ambient old parent represented by one parent of the final-core witness. -/
private noncomputable def lowerRouteFinalCoreParentEmbedding
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val) :
    Fin
        (schedule.lowerRouteFinalCoreScaleData
          packetCoordinate metricCore coordinate coordinateAfter).coarse.card ↪
      Fin (schedule.scaleData coordinate).coarse.card :=
  ((schedule.scaleData coordinate).cover.hitParentSubfamily
    (schedule.lowerRouteAmbientCoreFine
      (packetCoordinate := packetCoordinate) metricCore)).embedding

@[simp] private theorem lowerRouteFinalCoreScaleData_parent_ambient
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val)
    (source : Fin metricCore.restriction.fineSelected.family.card) :
    schedule.lowerRouteFinalCoreParentEmbedding
          packetCoordinate metricCore coordinate coordinateAfter
          ((schedule.lowerRouteFinalCoreScaleData
            packetCoordinate metricCore coordinate coordinateAfter
            ).cover.parent source) =
      (schedule.scaleData coordinate).cover.parent
        (metricCore.metric.mesh.complete.selectedFine.embedding
          (metricCore.restriction.fineSelected.embedding source)) := by
  let ambientData :=
    schedule.lowerRouteAmbientCoreScaleData
      packetCoordinate metricCore coordinate coordinateAfter
  let indexEquiv :=
    schedule.lowerRouteFinalToAmbientCoreEquiv packetCoordinate metricCore
  let tubeEq :=
    schedule.lowerRouteFinalToAmbientCoreEquiv_tube
      packetCoordinate metricCore
  change
    ((schedule.scaleData coordinate).cover.hitParentSubfamily
      (schedule.lowerRouteAmbientCoreFine
        (packetCoordinate := packetCoordinate) metricCore)).embedding
        ((ambientData.cover.reindex indexEquiv tubeEq).parent source) =
      (schedule.scaleData coordinate).cover.parent
        (metricCore.metric.mesh.complete.selectedFine.embedding
          (metricCore.restriction.fineSelected.embedding source))
  rw [ambientData.cover.reindex_parent_eq
    ambientData.rho_pos.le indexEquiv tubeEq]
  change
    ((schedule.scaleData coordinate).cover.hitParentSubfamily
      (schedule.lowerRouteAmbientCoreFine
        (packetCoordinate := packetCoordinate) metricCore)).embedding
        (((schedule.scaleData coordinate).cover.restrictToHitParents
          (schedule.lowerRouteAmbientCoreFine
            (packetCoordinate := packetCoordinate) metricCore)).parent
            (indexEquiv source)) =
      (schedule.scaleData coordinate).cover.parent
        (metricCore.metric.mesh.complete.selectedFine.embedding
          (metricCore.restriction.fineSelected.embedding source))
  rw [
    (schedule.scaleData coordinate).cover
      |>.restrictToHitParents_parent_eq
        (schedule.scaleData coordinate).rho_pos.le,
    (schedule.scaleData coordinate).cover.hitParent_ambient,
    schedule.lowerRouteFinalToAmbientCoreEquiv_embedding
      packetCoordinate metricCore
  ]

@[simp] private theorem lowerRouteFinalCoreScaleData_parent_tube
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val)
    (parent :
      Fin
        (schedule.lowerRouteFinalCoreScaleData
          packetCoordinate metricCore coordinate coordinateAfter).coarse.card) :
    (schedule.lowerRouteFinalCoreScaleData
        packetCoordinate metricCore coordinate coordinateAfter
        ).coarse.tube parent =
      (schedule.scaleData coordinate).coarse.tube
        (schedule.lowerRouteFinalCoreParentEmbedding
          packetCoordinate metricCore coordinate coordinateAfter parent) := by
  rfl

/--
Equality of descendant old parents forces equality of the packet-level metric
parents, using only laminar nesting and the fixed metric core.
-/
private theorem lowerRouteFinalOldParentEq_implies_metricParentEq
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val)
    (first second :
      Fin metricCore.restriction.fineSelected.family.card)
    (parentEq :
      (schedule.lowerRouteFinalCoreScaleData
          packetCoordinate metricCore coordinate coordinateAfter
          ).cover.parent first =
        (schedule.lowerRouteFinalCoreScaleData
          packetCoordinate metricCore coordinate coordinateAfter
          ).cover.parent second) :
    metricCore.metric.metricInput.packetParent
          (metricCore.metric.mesh.restrictedOldData.cover.parent
            (metricCore.restriction.fineSelected.embedding first)) =
      metricCore.metric.metricInput.packetParent
        (metricCore.metric.mesh.restrictedOldData.cover.parent
          (metricCore.restriction.fineSelected.embedding second)) := by
  have ambientParentEq :
      (schedule.scaleData coordinate).cover.parent
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding first)) =
        (schedule.scaleData coordinate).cover.parent
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding second)) := by
    rw [
      ← schedule.lowerRouteFinalCoreScaleData_parent_ambient
        packetCoordinate metricCore coordinate coordinateAfter first,
      ← schedule.lowerRouteFinalCoreScaleData_parent_ambient
        packetCoordinate metricCore coordinate coordinateAfter second,
      parentEq
    ]
  have packetParentEq :
      (schedule.scaleData packetCoordinate).cover.parent
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding first)) =
        (schedule.scaleData packetCoordinate).cover.parent
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding second)) :=
    schedule.parent_eq_of_coordinate_le
      packetCoordinate coordinate coordinateAfter.le _ _ ambientParentEq
  have cellEq :
      schedule.proxyPacketLineCell fineNonempty packetCoordinate width
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding first)) =
        schedule.proxyPacketLineCell fineNonempty packetCoordinate width
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding second)) :=
    schedule.proxyPacketLineCell_parent_invariant
      fineNonempty packetCoordinate width _ _ packetParentEq
  have section6ParentEq :=
    (metricCore.metricParent_eq_iff_proxyPacketLineCell_embedding_eq
      (metricCore.restriction.fineSelected.embedding first)
      (metricCore.restriction.fineSelected.embedding second)).2 cellEq
  simpa only [
    metricCore.metric.metricInput.section6_parent_eq_packetParent
  ] using section6ParentEq

/-- Every final genuine metric fiber is saturated at a descendant old level. -/
private theorem lowerRouteFinalMetricFiber_saturated
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    let scaleData :=
      schedule.lowerRouteFinalCoreScaleData
        packetCoordinate metricCore coordinate coordinateAfter
    ∀ first second,
      scaleData.cover.parent first = scaleData.cover.parent second →
        (first ∈
            wz2PaperFullFiberIndices
              metricCore.restriction.fineSelected.family
              metricCore.restriction.coarseSelected.family parent ↔
          second ∈
            wz2PaperFullFiberIndices
              metricCore.restriction.fineSelected.family
              metricCore.restriction.coarseSelected.family parent) := by
  dsimp only
  intro first second oldParentEq
  have metricParentEq :=
    schedule.lowerRouteFinalOldParentEq_implies_metricParentEq
      packetCoordinate metricCore coordinate coordinateAfter
      first second oldParentEq
  rw [mem_wz2PaperFullFiberIndices_iff,
    mem_wz2PaperFullFiberIndices_iff]
  have firstAmbient :
      WZ1PaperTubeCovers
          (metricCore.restriction.fineSelected.family.tube first)
          (metricCore.restriction.coarseSelected.family.tube parent) ↔
        metricCore.metric.metricInput.packetParent
            (metricCore.metric.mesh.restrictedOldData.cover.parent
              (metricCore.restriction.fineSelected.embedding first)) =
          metricCore.restriction.coarseSelected.embedding parent := by
    constructor
    · intro covered
      have ambientCovered :
          WZ1PaperTubeCovers
            (metricCore.metric.selectedFine.tube
              (metricCore.restriction.fineSelected.embedding first))
            (metricCore.metric.metricParents.tube
              (metricCore.restriction.coarseSelected.embedding parent)) := by
        simpa only [
          metricCore.restriction.fineSelected.tube_eq,
          metricCore.restriction.coarseSelected.tube_eq
        ] using covered
      exact
        pureWZ2_prop62_metricParent_unique
          metricCore.metric.metricInput.coarse_essentially_distinct
          (metricCore.restriction.fineSelected.embedding first)
          (metricCore.metric.metricInput.packetParent
            (metricCore.metric.mesh.restrictedOldData.cover.parent
              (metricCore.restriction.fineSelected.embedding first)))
          (metricCore.restriction.coarseSelected.embedding parent)
          (metricCore.metric.metricInput.packetParent_covers
            (metricCore.restriction.fineSelected.embedding first))
          ambientCovered
    · intro ambientParentEq
      have covered :=
        metricCore.metric.metricInput.packetParent_covers
          (metricCore.restriction.fineSelected.embedding first)
      rw [ambientParentEq] at covered
      simpa only [
        metricCore.restriction.fineSelected.tube_eq,
        metricCore.restriction.coarseSelected.tube_eq
      ] using covered
  have secondAmbient :
      WZ1PaperTubeCovers
          (metricCore.restriction.fineSelected.family.tube second)
          (metricCore.restriction.coarseSelected.family.tube parent) ↔
        metricCore.metric.metricInput.packetParent
            (metricCore.metric.mesh.restrictedOldData.cover.parent
              (metricCore.restriction.fineSelected.embedding second)) =
          metricCore.restriction.coarseSelected.embedding parent := by
    constructor
    · intro covered
      have ambientCovered :
          WZ1PaperTubeCovers
            (metricCore.metric.selectedFine.tube
              (metricCore.restriction.fineSelected.embedding second))
            (metricCore.metric.metricParents.tube
              (metricCore.restriction.coarseSelected.embedding parent)) := by
        simpa only [
          metricCore.restriction.fineSelected.tube_eq,
          metricCore.restriction.coarseSelected.tube_eq
        ] using covered
      exact
        pureWZ2_prop62_metricParent_unique
          metricCore.metric.metricInput.coarse_essentially_distinct
          (metricCore.restriction.fineSelected.embedding second)
          (metricCore.metric.metricInput.packetParent
            (metricCore.metric.mesh.restrictedOldData.cover.parent
              (metricCore.restriction.fineSelected.embedding second)))
          (metricCore.restriction.coarseSelected.embedding parent)
          (metricCore.metric.metricInput.packetParent_covers
            (metricCore.restriction.fineSelected.embedding second))
          ambientCovered
    · intro ambientParentEq
      have covered :=
        metricCore.metric.metricInput.packetParent_covers
          (metricCore.restriction.fineSelected.embedding second)
      rw [ambientParentEq] at covered
      simpa only [
        metricCore.restriction.fineSelected.tube_eq,
        metricCore.restriction.coarseSelected.tube_eq
      ] using covered
  rw [firstAmbient, secondAmbient, metricParentEq]

/-- The natural old-scale witness on one exact final metric fiber. -/
private noncomputable def lowerRouteMetricFiberDescendantScaleData
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val)
    (parent :
      Fin metricCore.restriction.coarseSelected.family.card) :
    WZ2PaperPureScaleCoverData
      (metricCore.restriction.metricFiberSource parent).family
      (schedule.actualScale coordinate)
      (ambientConstant * metricCore.quotientDensityLoss) :=
  pureWZ2_prop62_restrictScaleToSaturated
    (schedule.lowerRouteFinalCoreScaleData
      packetCoordinate metricCore coordinate coordinateAfter)
    (wz2PaperFullFiberIndices
      metricCore.restriction.fineSelected.family
      metricCore.restriction.coarseSelected.family parent)
    (by
      rcases metricCore.restriction.section6Cover.parent_hit parent with
        ⟨source, covered⟩
      exact
        ⟨source,
          (mem_wz2PaperFullFiberIndices_iff parent source).mpr covered⟩)
    (schedule.lowerRouteFinalMetricFiber_saturated
      packetCoordinate metricCore coordinate coordinateAfter parent)

private noncomputable def lowerRouteScaleDataCastParentEmbedding
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {scale : ℝ} {C : ENNReal} {α : Type*}
    (familyEq : source = target)
    (data : WZ2PaperPureScaleCoverData source scale C)
    (embedding : Fin data.coarse.card ↪ α) :
    Fin (familyEq ▸ data).coarse.card ↪ α := by
  subst target
  exact embedding

private theorem lowerRouteScaleDataCastParentEmbedding_tube
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {scale : ℝ} {C : ENNReal}
    {ambientCoarse : Kakeya.Streamlined.TubeFamily scale}
    (familyEq : source = target)
    (data : WZ2PaperPureScaleCoverData source scale C)
    (embedding : Fin data.coarse.card ↪ Fin ambientCoarse.card)
    (tubeEq : ∀ middle,
      data.coarse.tube middle = ambientCoarse.tube (embedding middle))
    (middle : Fin (familyEq ▸ data).coarse.card) :
    (familyEq ▸ data).coarse.tube middle =
      ambientCoarse.tube
        (lowerRouteScaleDataCastParentEmbedding
          familyEq data embedding middle) := by
  subst target
  exact tubeEq middle

private theorem lowerRouteScaleDataCastParentEmbedding_parent
    {source target : Kakeya.Streamlined.TubeFamily delta}
    {scale : ℝ} {C : ENNReal} {α : Type*}
    (familyEq : source = target)
    (data : WZ2PaperPureScaleCoverData source scale C)
    (embedding : Fin data.coarse.card ↪ α)
    (index : Fin target.card) :
    lowerRouteScaleDataCastParentEmbedding familyEq data embedding
        ((familyEq ▸ data).cover.parent index) =
      embedding
        (data.cover.parent
          (Fin.cast
            (congrArg Kakeya.Streamlined.TubeFamily.card familyEq.symm)
            index)) := by
  subst target
  rfl

private theorem lowerRouteSubfamilyEmbedding_cast
    {ambient : Kakeya.Streamlined.TubeFamily delta}
    {first second : WZ2PaperPureTubeSubfamily ambient}
    (subfamilyEq : first = second)
    (index : Fin second.family.card) :
    first.embedding
        (Fin.cast
          (congrArg
            (fun selected : WZ2PaperPureTubeSubfamily ambient =>
              selected.family.card)
            subfamilyEq.symm)
          index) =
      second.embedding index := by
  subst second
  rfl

/-- The same-receipt analytic descendant on one final genuine metric fiber. -/
private noncomputable def lowerRouteMetricFiberDescendantDataNatural
    (parent : Fin metricCore.restriction.coarseSelected.family.card)
    (coordinate : Fin schedule.levelCount)
    (coordinateAfter : packetCoordinate.val < coordinate.val) :
    PureWZ2Prop62ProxyQuotientFiberDescendantData
      metricCore (ambientConstant * metricCore.quotientDensityLoss)
        parent coordinate := by
  let data :=
    schedule.lowerRouteFinalCoreScaleData
      packetCoordinate metricCore coordinate coordinateAfter
  let indices :=
    wz2PaperFullFiberIndices
      metricCore.restriction.fineSelected.family
      metricCore.restriction.coarseSelected.family parent
  have indicesNonempty : indices.Nonempty := by
    rcases metricCore.restriction.section6Cover.parent_hit parent with
      ⟨source, covered⟩
    exact
      ⟨source,
        (mem_wz2PaperFullFiberIndices_iff parent source).mpr covered⟩
  let parents := pureWZ2Prop62SaturatedParents data indices
  let complete :=
    pureWZ2Prop62SaturatedCompleteRestriction
      data indices indicesNonempty
  let raw :=
    pureWZ2_prop62_completeParent_sameScale
      data parents
        (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)
  have indicesEq : complete.selectedFineIndices = indices :=
    pureWZ2Prop62SaturatedCompleteRestriction_indices_eq
      data indicesNonempty
      (schedule.lowerRouteFinalMetricFiber_saturated
        packetCoordinate metricCore coordinate coordinateAfter parent)
  have selectedFineEq :
      complete.selectedFine =
        metricCore.restriction.metricFiberSource parent := by
    unfold PureWZ2CompleteParentRestrictionData.selectedFine
    unfold PureWZ2Prop62MetricCoreRestrictionData.metricFiberSource
    rw [indicesEq]
  let familyEq :=
    congrArg WZ2PaperPureTubeSubfamily.family selectedFineEq
  let scaleData :
      WZ2PaperPureScaleCoverData
        (metricCore.restriction.metricFiberSource parent).family
        (schedule.actualScale coordinate)
        (ambientConstant * metricCore.quotientDensityLoss) :=
    familyEq ▸ raw
  let selectedParentEmbedding :
      Fin raw.coarse.card ↪ Fin data.coarse.card :=
    (data.cover.hitParentSubfamily complete.selectedFine).embedding
  let ambientParentEmbedding :
      Fin data.coarse.card ↪
        Fin (schedule.scaleData coordinate).coarse.card :=
    schedule.lowerRouteFinalCoreParentEmbedding
      packetCoordinate metricCore coordinate coordinateAfter
  let rawEmbedding :
      Fin raw.coarse.card ↪
        Fin (schedule.scaleData coordinate).coarse.card :=
    Function.Embedding.trans selectedParentEmbedding ambientParentEmbedding
  let parentEmbedding :
      Fin scaleData.coarse.card ↪
        Fin (schedule.scaleData coordinate).coarse.card :=
    lowerRouteScaleDataCastParentEmbedding familyEq raw rawEmbedding
  refine {
    scaleData := scaleData
    parent_embedding := parentEmbedding
    parent_tube_eq := ?_
    parent_commutes := ?_
  }
  · intro middle
    have rawTubeEq : ∀ rawMiddle,
        raw.coarse.tube rawMiddle =
          (schedule.scaleData coordinate).coarse.tube
            (rawEmbedding rawMiddle) := by
      intro rawMiddle
      change
        (data.cover.hitParentSubfamily complete.selectedFine).family.tube
            rawMiddle =
          (schedule.scaleData coordinate).coarse.tube
            (ambientParentEmbedding
              (selectedParentEmbedding rawMiddle))
      rw [(data.cover.hitParentSubfamily complete.selectedFine).tube_eq]
      exact
        schedule.lowerRouteFinalCoreScaleData_parent_tube
          packetCoordinate metricCore coordinate coordinateAfter
          (selectedParentEmbedding rawMiddle)
    exact
      lowerRouteScaleDataCastParentEmbedding_tube
        familyEq raw rawEmbedding rawTubeEq middle
  · intro source
    let rawSource : Fin complete.selectedFine.family.card :=
      Fin.cast
        (congrArg Kakeya.Streamlined.TubeFamily.card familyEq.symm)
        source
    have castParent :=
      lowerRouteScaleDataCastParentEmbedding_parent
        familyEq raw rawEmbedding source
    have rawParentAmbient :=
      pureWZ2_prop62_completeParent_sameScale_parent_ambient
        data parents
          (pureWZ2Prop62SaturatedParents_nonempty data indicesNonempty)
          rawSource
    have localEmbeddingEq :
        complete.selectedFine.embedding rawSource =
          (metricCore.restriction.metricFiberSource parent).embedding source :=
      lowerRouteSubfamilyEmbedding_cast selectedFineEq source
    have finalParentAmbient :=
      schedule.lowerRouteFinalCoreScaleData_parent_ambient
        packetCoordinate metricCore coordinate coordinateAfter
        ((metricCore.restriction.metricFiberSource parent).embedding source)
    calc
      parentEmbedding (scaleData.cover.parent source) =
          rawEmbedding (raw.cover.parent rawSource) := castParent
      _ = ambientParentEmbedding
          (selectedParentEmbedding (raw.cover.parent rawSource)) := rfl
      _ = ambientParentEmbedding
          (data.cover.parent (complete.selectedFine.embedding rawSource)) := by
            exact congrArg ambientParentEmbedding rawParentAmbient
      _ = ambientParentEmbedding
          (data.cover.parent
            ((metricCore.restriction.metricFiberSource parent).embedding
              source)) := by
            rw [localEmbeddingEq]
      _ = (schedule.scaleData coordinate).cover.parent
          (metricCore.metric.mesh.complete.selectedFine.embedding
            (metricCore.restriction.fineSelected.embedding
              ((metricCore.restriction.metricFiberSource parent).embedding
                source))) := finalParentAmbient
      _ = (schedule.scaleData coordinate).cover.parent
          (metricCore.metricFiberAmbientIndex parent source) := rfl

end PureWZ2Prop62LaminarPureSchedule

namespace PureWZ2Prop62ProxyQuotientFiberRouteDescendantData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {firstConstant secondConstant : ENNReal}
    {scaleFactor : ℝ}
    {parent : Fin metricCore.restriction.coarseSelected.family.card}
    {coordinate : Fin schedule.levelCount}

/-- Increasing only the CWA constant preserves one local route descendant. -/
noncomputable def mono
    (data :
      PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
        metricCore firstConstant scaleFactor parent coordinate)
    (constantLe : firstConstant ≤ secondConstant) :
    PureWZ2Prop62ProxyQuotientFiberRouteDescendantData
      metricCore secondConstant scaleFactor parent coordinate where
  actual := data.actual
  actual_eq_scaled := data.actual_eq_scaled
  scaleData := data.scaleData.mono constantLe
  partitioningCover := data.partitioningCover
  partitioningCover_eq := by
    simp only [WZ2PaperPureScaleCoverData.mono]
  coarse_line_class := data.coarse_line_class
  lineCover := data.lineCover
  lineCover_parent_eq := data.lineCover_parent_eq
  parent_near_anchor := data.parent_near_anchor
  separated := data.separated
  localization := data.localization

end PureWZ2Prop62ProxyQuotientFiberRouteDescendantData

/--
Concrete lower-route constructor at the fixed representative-middle scale.

The analytic descendant is constructed internally from the same cleanup
receipt.  The only loss between that witness and the returned route is the
explicit representative-middle John factor, paid by
`densityConstantAbsorption`.
-/
noncomputable def pureWZ2_prop62_metricParentsV4_lowerRoute
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow sourceConstant : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    (allScale :
      PureWZ2Prop62ProxyQuotientAllScaleColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore.metric upperColoring
          (pureWZ2Prop62RepresentativeParentScaledConflictScale schedule)
          (fun _ => pureWZ2Prop62RepresentativeParentScaledConflictDegree))
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        allScale.adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBoundedBase : HasBoundedBase fine 4)
    (rhoLeOne : rho ≤ 1)
    (scaleSeparation : 100 * delta ≤ rho)
    (sourceConstantFinite :
      WZ2PaperFiniteErrorConstant sourceConstant)
    (K : ℝ)
    (scaleFactorLeK :
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor ≤ K)
    (descendantActualSmall :
      ∀ coordinate : Fin schedule.levelCount,
        packetCoordinate.val < coordinate.val →
          schedule.actualScale coordinate ≤ 1 / 10000)
    (densityConstantAbsorption :
      pureWZ2Prop62MetricFiberRepresentativeMiddleJohnLoss *
          (ambientConstant * metricCore.quotientDensityLoss) ≤
        sourceConstant)
    (packetScaleLt :
      schedule.actualScale packetCoordinate <
        rho / K)
    (floorGate :
      scaleWindow * ENNReal.ofReal delta <
        ENNReal.ofReal (schedule.actualScale packetCoordinate))
    (scaledWindowAbsorption :
      (100 : ENNReal) *
          ENNReal.ofReal
            pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
          scaleWindow ≤
        (81000000 : ENNReal) * sourceConstant)
    (insertedSingletonTopGate :
      (4 : ENNReal) *
          ((100 : ENNReal) * scaleWindow * ENNReal.ofReal rho) ≤
        ((81000000 : ENNReal) * sourceConstant) *
          ENNReal.ofReal (schedule.actualScale packetCoordinate)) :
    PureWZ2Prop62ProxyQuotientFiberRouteInput
      schedule fineNonempty quotient width packetCoordinate
        strideBase weight metricCore sourceConstant where
  rho_le_one := rhoLeOne
  scale_separation := scaleSeparation
  source_constant_finite := sourceConstantFinite
  scaleFactor := pureWZ2Prop62MetricFiberRepresentativeMiddleFactor
  scaleFactor_one := by
    norm_num [
      pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
      pureWZ2Prop62RepresentativeParentScaledFactor]
  K := K
  scaleFactor_le_K := scaleFactorLeK
  packet_scale_lt_rho_div_K := packetScaleLt
  fine_bounded_base := fineBoundedBase
  floor_gate := floorGate
  scaled_window_absorption := scaledWindowAbsorption
  inserted_singleton_top_gate := insertedSingletonTopGate
  descendant := by
    intro parent coordinate coordinateAfter
    have fineBaseFive :
        ∀ source, ‖(fine.tube source).base‖ ≤ 5 := by
      intro source
      exact (fineBoundedBase source).trans (by norm_num)
    have factorPos :
        0 <
          (pureWZ2Prop62MetricFiberRepresentativeMiddleFactor : ℝ) := by
      norm_num [
        pureWZ2Prop62MetricFiberRepresentativeMiddleFactor,
        pureWZ2Prop62RepresentativeParentScaledFactor]
    have KPos : 0 < K :=
      factorPos.trans_le scaleFactorLeK
    have coordinateLePacket :
        schedule.actualScale coordinate ≤
          schedule.actualScale packetCoordinate :=
      schedule.actualScale_antitone
        packetCoordinate coordinate coordinateAfter.le
    have packetMulLt :
        schedule.actualScale packetCoordinate *
            K < rho :=
      (lt_div_iff₀ KPos).mp packetScaleLt
    have actualLeRho :
        pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
            schedule.actualScale coordinate ≤ rho := by
      calc
        pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
              schedule.actualScale coordinate ≤
            pureWZ2Prop62MetricFiberRepresentativeMiddleFactor *
              schedule.actualScale packetCoordinate :=
          mul_le_mul_of_nonneg_left coordinateLePacket factorPos.le
        _ ≤ K * schedule.actualScale packetCoordinate := by
          exact
            mul_le_mul_of_nonneg_right scaleFactorLeK
              (schedule.scaleData packetCoordinate).rho_pos.le
        _ = schedule.actualScale packetCoordinate * K := by ring
        _ ≤ rho := packetMulLt.le
    let represented :=
      pureWZ2_prop62_metricFiber_representativeRouteDescendant
        schedule packetCoordinate metricCore allScale preliminary_eq
        fineLine fineBaseFive parent coordinate
        (schedule.lowerRouteMetricFiberDescendantDataNatural
          packetCoordinate metricCore parent coordinate coordinateAfter)
        (descendantActualSmall coordinate coordinateAfter)
        (by rfl)
        rhoLeOne fineBoundedBase actualLeRho
    exact represented.mono densityConstantAbsorption

end Kakeya.Assouad

end
