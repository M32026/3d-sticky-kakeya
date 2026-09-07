import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberDensitySelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCompleteParentRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureNearbyTree
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SameAxisThickening

/-!
# The actual singleton scale of one complete strict fiber

Restrict a literal Definition 2.12 scale witness to one complete strict
parent fiber.  At the same actual scale the restricted family has one coarse
parent, its full fiber is the whole restricted family, and its actual-John CWA
is the ambient parent's canonical witness up to exact finite reindexing.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable
open MeasureTheory

/--
Selecting one actual parent by the complete-parent constructor gives exactly
the public complete strict full-fiber index set.
-/
theorem pureWZ2_singletonComplete_selectedFineIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (rhoNonnegative : 0 ≤ rho)
    (parent : Fin coarse.card) :
    (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      cover ({parent} : Finset (Fin coarse.card))
      (Finset.singleton_nonempty parent)).selectedFineIndices =
        wz2PaperOrdinaryFullFiberIndices fine coarse parent := by
  ext source
  simp only [
    PureWZ2CompleteParentRestrictionData.selectedFineIndices,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton
  ]
  rw [cover.mem_fullFiber_iff_parent_eq rhoNonnegative]

/-- Every canonical singleton-complete selected tube lies in that parent. -/
theorem pureWZ2_singletonComplete_tube_subset_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (rhoNonnegative : 0 ≤ rho)
    (parent : Fin coarse.card)
    (index :
      Fin
        (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
          cover ({parent} : Finset (Fin coarse.card))
          (Finset.singleton_nonempty parent)).selectedFine.family.card) :
    ((PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      cover ({parent} : Finset (Fin coarse.card))
      (Finset.singleton_nonempty parent)).selectedFine.family.tube
        index).carrier ⊆
      (coarse.tube parent).carrier := by
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      cover ({parent} : Finset (Fin coarse.card))
      (Finset.singleton_nonempty parent)
  rw [complete.selectedFine.tube_eq]
  apply
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent (complete.selectedFine.embedding index)).mp
  rw [← pureWZ2_singletonComplete_selectedFineIndices
    cover rhoNonnegative parent]
  exact complete.selectedFine_embedding_mem index

/--
Expose the dense complete fiber through the canonical complete-parent family
used by the scale-restriction lemmas.
-/
theorem pureWZ2_exists_completeParent_density
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (rhoNonnegative : 0 ≤ rho)
    (fineNonempty : fine.Nonempty)
    (shading : Kakeya.Streamlined.TubeShading fine)
    (density : ENNReal)
    (sourceDense :
      density * fine.toBodyFamily.mass ≤ shading.mass) :
    ∃ parent : Fin coarse.card,
      let complete :=
        PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
          cover ({parent} : Finset (Fin coarse.card))
          (Finset.singleton_nonempty parent)
      density * complete.selectedFine.family.toBodyFamily.mass ≤
        (complete.selectedFine.toTubeSubfamily.restrictShading shading).mass := by
  rcases
      pureWZ2_exists_completeFiber_density_parent
        cover rhoNonnegative fineNonempty shading density sourceDense
    with ⟨parent, parentDense⟩
  refine ⟨parent, ?_⟩
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      cover ({parent} : Finset (Fin coarse.card))
      (Finset.singleton_nonempty parent)
  have indicesEq :
      complete.selectedFineIndices =
        wz2PaperOrdinaryFullFiberIndices fine coarse parent :=
    pureWZ2_singletonComplete_selectedFineIndices
      cover rhoNonnegative parent
  dsimp only
  rw [tubeFamily_mass_eq_nominal]
  change
    density *
        ((complete.selectedFineIndices.card : ENNReal) *
          Kakeya.deltaTubeVolume delta) ≤
      ∑ index : Fin complete.selectedFineIndices.card,
        volume
          (shading.carrier
            (complete.selectedFineIndices.orderEmbOfFin rfl index))
  rw [tubeFamily_mass_eq_nominal] at parentDense
  change
    density *
        (((wz2PaperOrdinaryFullFiberIndices
          fine coarse parent).card : ENNReal) *
          Kakeya.deltaTubeVolume delta) ≤
      ∑ index :
          Fin (wz2PaperOrdinaryFullFiberIndices
            fine coarse parent).card,
        volume
          (shading.carrier
            ((wz2PaperOrdinaryFullFiberIndices
              fine coarse parent).orderEmbOfFin rfl index))
    at parentDense
  rw [indicesEq]
  exact parentDense

/--
The complete strict fiber over one actual parent carries a one-parent pure
scale witness at the same actual scale with no CWA loss.
-/
noncomputable def pureWZ2_completeFiber_actualScale
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (scale : WZ2PaperPureScaleCoverData fine rho C)
    (COne : 1 ≤ C)
    (parent : Fin scale.coarse.card) :
    WZ2PaperPureScaleCoverData
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        scale.cover ({parent} : Finset (Fin scale.coarse.card))
        (Finset.singleton_nonempty parent)).selectedFine.family rho C := by
  let selectedParents : Finset (Fin scale.coarse.card) := {parent}
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      scale.cover selectedParents (Finset.singleton_nonempty parent)
  let selectedCoarse :=
    scale.cover.hitParentSubfamily complete.selectedFine
  let restrictedCover :=
    scale.cover.restrictToHitParents complete.selectedFine
  have nested :
      ∀ first second,
        scale.cover.parent first = scale.cover.parent second →
          scale.cover.parent first = scale.cover.parent second :=
    fun _ _ equality => equality
  have selectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        complete.selectedFine.family selectedCoarse.family C :=
    complete.finer_restricted_fullFiber_uniform
      scale.cover scale.rho_pos.le nested scale.full_fiber_uniform
  have fiberRatio :
      ∀ selectedParent : Fin selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
            fine scale.coarse
              (selectedCoarse.embedding selectedParent) ≤
          (1 : ENNReal) *
            wz2PaperOrdinaryFullFiberCount
              complete.selectedFine.family
              selectedCoarse.family selectedParent := by
    intro selectedParent
    have completeFiber :=
      complete.finer_hit_fullFiber_complete
        scale.cover scale.rho_pos.le nested selectedParent
    rw [one_mul, wz2PaperOrdinaryFullFiberCount,
      wz2PaperOrdinaryFullFiberCount]
    have cardEquality :
        (wz2PaperOrdinaryFullFiberIndices
          complete.selectedFine.family selectedCoarse.family
          selectedParent).card =
        (wz2PaperOrdinaryFullFiberIndices
          fine scale.coarse
          (selectedCoarse.embedding selectedParent)).card := by
      rw [← completeFiber]
      exact
        Finset.card_image_of_injective _
          complete.selectedFine.embedding.injective |>.symm
    exact_mod_cast cardEquality.symm.le
  let raw :=
    scale.restrict
      complete.selectedFine selectedCoarse restrictedCover
      selectedUniform fiberRatio
  have constantEq :
      max C ((1 : ENNReal) * C) = C := by
    simp
  simpa [raw, constantEq] using raw

/--
At every ambient scale sufficiently finer than the selected actual scale, the
whole selected actual fiber is a union of complete ambient fibers.  Hence the
ambient pure scale witness restricts with no CWA loss.
-/
noncomputable def pureWZ2_completeFiber_finerScale
    {delta actual finer : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualC finerC : ENNReal}
    (actualScale : WZ2PaperPureScaleCoverData fine actual actualC)
    (finerScale : WZ2PaperPureScaleCoverData fine finer finerC)
    (parent : Fin actualScale.coarse.card)
    (deltaFiner : delta ≤ finer)
    (deltaActual : delta ≤ actual)
    (gap : 4 * (finer - delta) ≤ actual) :
    WZ2PaperPureScaleCoverData
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        actualScale.cover ({parent} : Finset (Fin actualScale.coarse.card))
        (Finset.singleton_nonempty parent)).selectedFine.family
      finer finerC := by
  let selectedParents : Finset (Fin actualScale.coarse.card) := {parent}
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      actualScale.cover selectedParents
      (Finset.singleton_nonempty parent)
  let selectedCoarse :=
    finerScale.cover.hitParentSubfamily complete.selectedFine
  let restrictedCover :=
    finerScale.cover.restrictToHitParents complete.selectedFine
  have nested :
      ∀ first second,
        finerScale.cover.parent first =
            finerScale.cover.parent second →
          actualScale.cover.parent first =
            actualScale.cover.parent second :=
    finerScale.cover.parent_maps_nested_of_gap
      actualScale.cover
      actualScale.delta_pos.le
      finerScale.rho_pos actualScale.rho_pos
      deltaFiner deltaActual
      gap
  have selectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        complete.selectedFine.family selectedCoarse.family finerC :=
    complete.finer_restricted_fullFiber_uniform
      finerScale.cover finerScale.rho_pos.le nested
      finerScale.full_fiber_uniform
  have fiberRatio :
      ∀ selectedParent : Fin selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
            fine finerScale.coarse
              (selectedCoarse.embedding selectedParent) ≤
          (1 : ENNReal) *
            wz2PaperOrdinaryFullFiberCount
              complete.selectedFine.family selectedCoarse.family
              selectedParent := by
    intro selectedParent
    have completeFiber :=
      complete.finer_hit_fullFiber_complete
        finerScale.cover finerScale.rho_pos.le nested selectedParent
    rw [one_mul, wz2PaperOrdinaryFullFiberCount,
      wz2PaperOrdinaryFullFiberCount]
    have cardEquality :
        (wz2PaperOrdinaryFullFiberIndices
          complete.selectedFine.family selectedCoarse.family
          selectedParent).card =
        (wz2PaperOrdinaryFullFiberIndices
          fine finerScale.coarse
          (selectedCoarse.embedding selectedParent)).card := by
      rw [← completeFiber]
      exact
        Finset.card_image_of_injective _
          complete.selectedFine.embedding.injective |>.symm
    exact_mod_cast cardEquality.symm.le
  let raw :=
    finerScale.restrict
      complete.selectedFine selectedCoarse restrictedCover
      selectedUniform fiberRatio
  simpa [raw] using raw

/--
Package one coarser singleton parent once the target canonical John fiber CWA
has been transported.
-/
noncomputable def pureWZ2_completeFiber_coarserScale_of_fiberCWA
    {delta actual coarser : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualC outputC : ENNReal}
    (actualScale : WZ2PaperPureScaleCoverData fine actual actualC)
    (parent : Fin actualScale.coarse.card)
    (actualLeCoarser : actual ≤ coarser)
    (coarserPos : 0 < coarser)
    (outputOne : 1 ≤ outputC)
    (targetFiberCWA :
      let complete :=
        PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
          actualScale.cover
          ({parent} : Finset (Fin actualScale.coarse.card))
          (Finset.singleton_nonempty parent)
      let coarse : Kakeya.Streamlined.TubeFamily coarser :=
        {
          card := 1
          tube := fun _ =>
            sameAxisTube (rho := coarser)
              (actualScale.coarse.tube parent)
        }
      let normalization :=
        WZ2PaperAssouadUnitRescalingData.ofTube
          (coarse.tube 0) coarserPos
      WZ2PaperBodyConvexWolffBound
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := complete.selectedFine.family)
          (coarse := coarse) 0 normalization)
        outputC) :
    WZ2PaperPureScaleCoverData
      (PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
        actualScale.cover
        ({parent} : Finset (Fin actualScale.coarse.card))
        (Finset.singleton_nonempty parent)).selectedFine.family
      coarser outputC := by
  let complete :=
    PureWZ2CompleteParentRestrictionData.pureWZ2CompleteParentRestriction
      actualScale.cover
      ({parent} : Finset (Fin actualScale.coarse.card))
      (Finset.singleton_nonempty parent)
  let coarse : Kakeya.Streamlined.TubeFamily coarser :=
    {
      card := 1
      tube := fun _ =>
        sameAxisTube (rho := coarser)
          (actualScale.coarse.tube parent)
    }
  let cover :
      WZ2PaperPurePartitioningCover
        complete.selectedFine.family coarse :=
    {
      covers := by
        intro index
        refine ⟨0, ?_⟩
        rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
        exact
          (pureWZ2_singletonComplete_tube_subset_parent
            actualScale.cover actualScale.rho_pos.le parent index).trans
            (sameAxisTube_carrier_mono
              actualLeCoarser (actualScale.coarse.tube parent))
      doubled_fibers_disjoint := by
        intro first second distinct
        exact
          (distinct
            ((Fin.eq_zero first).trans
              (Fin.eq_zero second).symm)).elim
    }
  have fullFiber :
      wz2PaperOrdinaryFullFiberIndices
          complete.selectedFine.family coarse 0 =
        Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro index
    exact cover.parent_mem_fullFiber index
  have uniform :
      WZ2PaperPureFullFibersAreCUniform
        complete.selectedFine.family coarse outputC := by
    intro first second
    have firstEq : first = 0 := Fin.eq_zero first
    have secondEq : second = 0 := Fin.eq_zero second
    subst first
    subst second
    rw [wz2PaperOrdinaryFullFiberCount, fullFiber]
    simpa using
      mul_le_mul_right'
        outputOne
        (complete.selectedFine.family.card : ENNReal)
  let normalization :=
    WZ2PaperAssouadUnitRescalingData.ofTube
      (coarse.tube 0) coarserPos
  exact
    {
      delta_pos := actualScale.delta_pos
      rho_pos := coarserPos
      coarse := coarse
      cover := cover
      full_fiber_uniform := uniform
      rescaledFiber := fun targetParent => by
        have targetParentEq : targetParent = 0 :=
          Fin.eq_zero targetParent
        subst targetParent
        exact
          ⟨{
            normalization := normalization
            convex_wolff := targetFiberCWA
          }⟩
    }

end Kakeya.Assouad

end
