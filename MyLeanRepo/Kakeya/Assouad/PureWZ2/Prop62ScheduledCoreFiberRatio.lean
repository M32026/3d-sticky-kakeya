import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureSchedule

/-!
# Proposition 6.2: scheduled fiber ratio from an arbitrary node-density coefficient

The existing tree helper uses the special coefficient `2^depth` produced by
its own one-pass pruning.  The later simultaneous four-degree core has the
paper coefficient `2^L * A0`.  Replacing it by `2^(L+A0)` would destroy the
polylogarithmic loss.

This module proves the same strict-fiber cardinality ratio with an arbitrary
natural node-density coefficient.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62PureSchedule

variable
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow)

theorem selectedFullFiber_count_le_of_core_densityConstant
    (coordinate : Fin schedule.levelCount)
    (densityConstant : ℕ)
    {selected core : Finset (Fin fine.card)}
    (selectedNonempty : selected.Nonempty)
    (core_subset : core ⊆ selected)
    (node_density :
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
    (schedule.scaleData coordinate).cover.hitParentSubfamily
      coreFine
  rcases
      (schedule.scaleData coordinate).cover.hitParent_surjective
        coreFine parent
    with ⟨source, sourceParent⟩
  let leaf := coreFine.embedding source
  have leafCore : leaf ∈ core := by
    exact Finset.orderEmbOfFin_mem core rfl source
  have leafFiber :
      leaf ∈
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ leaf, rfl⟩
  have coreFiberNonempty :
      (core ∩
        schedule.tree.fiber
          (coordinate.1 + 1)
          (schedule.nodeAt (coordinate.1 + 1) leaf)).Nonempty :=
    ⟨leaf, Finset.mem_inter.mpr ⟨leafCore, leafFiber⟩⟩
  have densityNat :=
    node_density
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
        rw [ENNReal.mul_inv_cancel
          selectedPos.ne' selectedFinite]
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
        rcases Finset.mem_image.mp indexMem with
          ⟨target, _targetUniv, rfl⟩
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
    rw [schedule.tree_fiber_coordinate_nodeAt_eq_fullFiber
      coordinate leaf]
  rw [
    wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount,
    ← parentEq,
    ← schedule.tree_fiber_coordinate_nodeAt_eq_fullFiber
      coordinate leaf,
    coreFiberCard
  ]
  exact fiberBound

end PureWZ2Prop62PureSchedule

end Kakeya.Assouad

end
