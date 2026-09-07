import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62LineParameterMesh
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCompleteParentRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction

/-!
# Proposition 6.2 metric parents: same-scale complete-parent restriction

Selecting old scale parents and retaining all of their strict fibers preserves
the old literal pure scale witness with no CWA loss.  Every restricted strict
fiber is an exact finite reindexing of the corresponding ambient fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

noncomputable def pureWZ2_prop62_completeParent_sameScale
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (selectedParents : Finset (Fin data.coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty) :
    WZ2PaperPureScaleCoverData
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        data.cover selectedParents selectedParentsNonempty).selectedFine.family
      scale C := by
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      data.cover selectedParents selectedParentsNonempty
  let selectedCoarse :=
    data.cover.hitParentSubfamily complete.selectedFine
  let restrictedCover :=
    data.cover.restrictToHitParents complete.selectedFine
  have nested :
      ∀ first second,
        data.cover.parent first = data.cover.parent second →
          data.cover.parent first = data.cover.parent second :=
    fun _ _ equality => equality
  have selectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        complete.selectedFine.family selectedCoarse.family C :=
    complete.finer_restricted_fullFiber_uniform
      data.cover data.rho_pos.le nested data.full_fiber_uniform
  have fiberRatio :
      ∀ parent : Fin selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
            fine data.coarse (selectedCoarse.embedding parent) ≤
          (1 : ENNReal) *
            wz2PaperOrdinaryFullFiberCount
              complete.selectedFine.family
              selectedCoarse.family parent := by
    intro parent
    have completeFiber :=
      complete.finer_hit_fullFiber_complete
        data.cover data.rho_pos.le nested parent
    rw [one_mul, wz2PaperOrdinaryFullFiberCount,
      wz2PaperOrdinaryFullFiberCount]
    have cardEquality :
        (wz2PaperOrdinaryFullFiberIndices
          complete.selectedFine.family selectedCoarse.family
          parent).card =
        (wz2PaperOrdinaryFullFiberIndices
          fine data.coarse (selectedCoarse.embedding parent)).card := by
      rw [← completeFiber]
      exact
        (Finset.card_image_of_injective _
          complete.selectedFine.embedding.injective).symm
    exact_mod_cast cardEquality.symm.le
  let restricted :=
    data.restrict complete.selectedFine selectedCoarse
      restrictedCover selectedUniform fiberRatio
  refine
    {
      delta_pos := data.delta_pos
      rho_pos := data.rho_pos
      coarse := selectedCoarse.family
      cover := restrictedCover
      full_fiber_uniform := selectedUniform
      rescaledFiber := ?_
    }
  intro parent
  convert restricted.rescaledFiber parent using 1 <;>
    simp only [one_mul, max_self] <;>
    constructor <;> exact id

theorem pureWZ2_prop62_completeParent_sameScale_coarse
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (selectedParents : Finset (Fin data.coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty) :
    (pureWZ2_prop62_completeParent_sameScale
        data selectedParents selectedParentsNonempty).coarse =
      (data.cover.hitParentSubfamily
        (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
          data.cover selectedParents selectedParentsNonempty).selectedFine).family := by
  simp [pureWZ2_prop62_completeParent_sameScale]

/--
The parent of the same-scale complete restriction maps back to the original
ambient parent of the corresponding selected fine tube.
-/
theorem pureWZ2_prop62_completeParent_sameScale_parent_ambient
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (selectedParents : Finset (Fin data.coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty)
    (source : Fin
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        data.cover selectedParents
        selectedParentsNonempty).selectedFine.family.card) :
    let complete :=
      PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        data.cover selectedParents selectedParentsNonempty
    let restricted :=
      pureWZ2_prop62_completeParent_sameScale
        data selectedParents selectedParentsNonempty
    let selectedCoarse :=
      data.cover.hitParentSubfamily complete.selectedFine
    selectedCoarse.embedding (restricted.cover.parent source) =
      data.cover.parent (complete.selectedFine.embedding source) := by
  dsimp only
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      data.cover selectedParents selectedParentsNonempty
  let selectedCoarse :=
    data.cover.hitParentSubfamily complete.selectedFine
  let restricted :=
    pureWZ2_prop62_completeParent_sameScale
      data selectedParents selectedParentsNonempty
  have parentEq :
      restricted.cover.parent source =
        data.cover.hitParent complete.selectedFine source := by
    apply restricted.cover.fullFiber_parent_unique data.rho_pos.le
    · exact restricted.cover.parent_mem_fullFiber source
    · rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
      change
        (complete.selectedFine.family.tube source).carrier ⊆
          (selectedCoarse.family.tube
            (data.cover.hitParent complete.selectedFine source)).carrier
      rw [complete.selectedFine.tube_eq,
        selectedCoarse.tube_eq,
        data.cover.hitParent_ambient]
      exact
        (mem_wz2PaperOrdinaryFullFiberIndices_iff
          (data.cover.parent (complete.selectedFine.embedding source))
          (complete.selectedFine.embedding source)).mp
          (data.cover.parent_mem_fullFiber
            (complete.selectedFine.embedding source))
  rw [parentEq]
  exact data.cover.hitParent_ambient complete.selectedFine source

/--
The synchronized strict line cover is preserved by a complete-parent
same-scale restriction.
-/
theorem pureWZ2_prop62_completeParent_sameScale_parent_covers
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (selectedParents : Finset (Fin data.coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty)
    (parentCovers :
      ∀ source,
        WZ1PaperTubeCovers
          (fine.tube source)
          (data.coarse.tube (data.cover.parent source)))
    (source : Fin
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        data.cover selectedParents
        selectedParentsNonempty).selectedFine.family.card) :
    let complete :=
      PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        data.cover selectedParents selectedParentsNonempty
    let restricted :=
      pureWZ2_prop62_completeParent_sameScale
        data selectedParents selectedParentsNonempty
    WZ1PaperTubeCovers
      (complete.selectedFine.family.tube source)
      (restricted.coarse.tube (restricted.cover.parent source)) := by
  dsimp only
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      data.cover selectedParents selectedParentsNonempty
  let restricted :=
    pureWZ2_prop62_completeParent_sameScale
      data selectedParents selectedParentsNonempty
  let selectedCoarse :=
    data.cover.hitParentSubfamily complete.selectedFine
  have parentAmbient :=
    pureWZ2_prop62_completeParent_sameScale_parent_ambient
      data selectedParents selectedParentsNonempty source
  change
    WZ1PaperTubeCovers
      (complete.selectedFine.family.tube source)
      (selectedCoarse.family.tube (restricted.cover.parent source))
  rw [complete.selectedFine.tube_eq,
    selectedCoarse.tube_eq, parentAmbient]
  exact parentCovers (complete.selectedFine.embedding source)

end Kakeya.Assouad

end
