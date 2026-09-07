import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CallerFiberScale
import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedOneParentRestrictedSchedule

/-!
# Pure actual-John data on a selected one-parent schedule

At every coordinate finer than the caller, first construct the pure scale
witness on the complete caller fiber.  Then restrict that witness to the
already selected family and exactly the historical hit-parent coarse family.

The caller-fiber witness stored by the historical schedule need not be the
same proof choice as the one used by the pure construction.  Their retained
coarse families and covers are nevertheless identified through their common
prepared ambient cover before the weighted restriction is applied.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The weighted pure restriction loss before comparison with the historical
restricted-schedule constant. -/
def wz2PaperPreparedOneParentPureRestrictionConstant
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection) : ENNReal :=
  max quantitative.selectedUniformConstant
    ((quantitative.weight⁻¹ *
        (prepared.structuralConstant *
          quantitative.cardinalityRetentionConstant *
          quantitative.selectedUniformConstant)) *
      prepared.structuralConstant)

/-- A constant retaining both the historical restricted witness and the pure
actual-John restriction constructed here. -/
def wz2PaperPreparedOneParentPureScheduleConstant
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection)
    (restrictedConstant : ENNReal) : ENNReal :=
  max restrictedConstant
    (wz2PaperPreparedOneParentPureRestrictionConstant
      prepared parent selection quantitative)

/-- The historical absorption hypothesis makes the explicit maximum equal to
the existing restricted-schedule constant. -/
theorem wz2PaperPreparedOneParentPureScheduleConstant_eq
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection)
    (restrictedConstant : ENNReal)
    (hAbsorb :
      wz2PaperPreparedOneParentPureRestrictionConstant
          prepared parent selection quantitative ≤
        restrictedConstant) :
    wz2PaperPreparedOneParentPureScheduleConstant
        prepared parent selection quantitative restrictedConstant =
      restrictedConstant := by
  exact max_eq_left hAbsorb

private theorem callerFiberScaleData_coarse_eq
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {parent : Fin prepared.callerStrict.coarse.card}
    {coordinate : Fin prepared.strictScaleCount}
    (first second :
      WZ2PaperCallerFiberScaleData
        prepared parent coordinate) :
    first.scaleData.coarse = second.scaleData.coarse :=
  first.coarse_eq.trans second.coarse_eq.symm

private theorem callerFiberScaleData_cover_eq
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    {prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent}
    {parent : Fin prepared.callerStrict.coarse.card}
    {coordinate : Fin prepared.strictScaleCount}
    (first second :
      WZ2PaperCallerFiberScaleData
        prepared parent coordinate) :
    HEq first.scaleData.cover second.scaleData.cover :=
  first.cover_eq.trans second.cover_eq.symm

private noncomputable def
    WZ2PaperPureInternalCoverSynchronization.ofCoarseCoverHEq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {firstCoarse secondCoarse :
      Kakeya.Streamlined.TubeFamily rho}
    {firstCover :
      WZ2PaperPartitioningCover fine firstCoarse}
    {secondCover :
      WZ2PaperPartitioningCover fine secondCoarse}
    (synchronization :
      WZ2PaperPureInternalCoverSynchronization
        fine firstCoarse firstCover)
    (coarse_eq : firstCoarse = secondCoarse)
    (cover_eq : HEq firstCover secondCover) :
    WZ2PaperPureInternalCoverSynchronization
      fine secondCoarse secondCover := by
  subst secondCoarse
  rw [heq_iff_eq] at cover_eq
  subst secondCover
  exact synchronization

private theorem selected_uniform_of_coarse_cover_heq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {firstCoarse secondCoarse :
      Kakeya.Streamlined.TubeFamily rho}
    {firstCover :
      WZ2PaperPartitioningCover fine firstCoarse}
    {secondCover :
      WZ2PaperPartitioningCover fine secondCoarse}
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (selectedConstant : ENNReal)
    (coarse_eq : firstCoarse = secondCoarse)
    (cover_eq : HEq firstCover secondCover)
    (uniform :
      ∀ first second :
          Fin (firstCover.hitParentSubfamily selected).family.card,
        wz2PaperFullFiberCount
            selected.family
            (firstCover.hitParentSubfamily selected).family first ≤
          selectedConstant *
            wz2PaperFullFiberCount
              selected.family
              (firstCover.hitParentSubfamily selected).family second) :
    ∀ first second :
        Fin (secondCover.hitParentSubfamily selected).family.card,
      wz2PaperFullFiberCount
          selected.family
          (secondCover.hitParentSubfamily selected).family first ≤
        selectedConstant *
          wz2PaperFullFiberCount
            selected.family
            (secondCover.hitParentSubfamily selected).family second := by
  subst secondCoarse
  rw [heq_iff_eq] at cover_eq
  subst secondCover
  exact uniform

/-- Per-coordinate pure scale data on the final selected family, with exact
provenance to the existing historical restricted schedule. -/
structure WZ2PaperPreparedOneParentPureScheduleData
    {delta sigma sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma sourceLoss source shading)
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection)
    (restrictedConstant : ENNReal)
    (restricted :
      WZ2PaperPreparedOneParentRestrictedScheduleData
        prepared parent selection restrictedConstant) where
  callerFiberPureData :
    ∀ coordinate :
        Fin (wz2PaperPreparedOneParentFineScaleCount
          prepared parent),
      WZ2PaperCallerFiberPureScaleData
        aligned prepared parent
          (wz2PaperPreparedOneParentFineCoordinate
            prepared parent coordinate)
  synchronization :
    ∀ coordinate :
        Fin (wz2PaperPreparedOneParentFineScaleCount
          prepared parent),
      WZ2PaperPureInternalCoverSynchronization
        selection.refinement.selected.family
        (restricted.scaleData coordinate).coarse
        (restricted.scaleData coordinate).cover
  pureScale :
    ∀ coordinate :
        Fin (wz2PaperPreparedOneParentFineScaleCount
          prepared parent),
      WZ2PaperPureScaleCoverData
        selection.refinement.selected.family
        (prepared.strictScale
          (wz2PaperPreparedOneParentFineCoordinate
            prepared parent coordinate)).1
        (wz2PaperPreparedOneParentPureScheduleConstant
          prepared parent selection quantitative restrictedConstant)
  coarse_eq :
    ∀ coordinate,
      (pureScale coordinate).coarse =
        (restricted.scaleData coordinate).coarse
  cover_eq :
    ∀ coordinate,
      HEq (pureScale coordinate).cover
        (synchronization coordinate).publicCover

namespace WZ2PaperAlignedPureExactSource

/--
Restrict complete caller-fiber actual-John data to every coordinate of an
existing one-parent historical schedule.

The output constant is the maximum of the historical constant and the
weighted pure-restriction constant.  In the standard producer the latter is
the core term already absorbed by `restrictedConstant`.
-/
noncomputable def preparedOneParentPureScheduleData
    {delta sigma sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (aligned :
      WZ2PaperAlignedPureExactSource
        sigma sourceLoss source shading)
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (parent : Fin prepared.callerStrict.coarse.card)
    (selection :
      WZ2PaperPreparedOneParentSelectionData prepared parent)
    (quantitative :
      WZ2PaperPreparedOneParentQuantitativeData
        prepared parent selection)
    (restrictedConstant : ENNReal)
    (restricted :
      WZ2PaperPreparedOneParentRestrictedScheduleData
        prepared parent selection restrictedConstant) :
    WZ2PaperPreparedOneParentPureScheduleData
      aligned prepared parent selection quantitative
        restrictedConstant restricted := by
  let callerFiberPureData :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperCallerFiberPureScaleData
          aligned prepared parent
            (wz2PaperPreparedOneParentFineCoordinate
              prepared parent coordinate) :=
    fun coordinate =>
      aligned.callerFiberScaleData
        prepared parent
        (wz2PaperPreparedOneParentFineCoordinate
          prepared parent coordinate)
        (wz2PaperPreparedOneParentFineCoordinate_le
          prepared parent coordinate)
  let fiberSynchronization :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperPureInternalCoverSynchronization
          (wz2PaperPreparedOneParentFiber
            prepared parent).family
          (restricted.callerFiberData coordinate).scaleData.coarse
          (restricted.callerFiberData coordinate).scaleData.cover :=
    fun coordinate =>
      let pureData := callerFiberPureData coordinate
      let canonicalSynchronization :=
        aligned.canonicalSynchronizationFor prepared
      let synchronization :=
        pureData.historical.synchronization
          canonicalSynchronization
      synchronization.ofCoarseCoverHEq
        (callerFiberScaleData_coarse_eq
          pureData.historical
          (restricted.callerFiberData coordinate))
        (callerFiberScaleData_cover_eq
          pureData.historical
          (restricted.callerFiberData coordinate))
  let selectedSynchronization :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperPureInternalCoverSynchronization
          selection.refinement.selected.family
          (((restricted.callerFiberData coordinate).scaleData.cover
            |>.hitParentSubfamily
              selection.refinement.selected)).family
          ((restricted.callerFiberData coordinate).scaleData.cover
            |>.restrictToHitParents
              selection.refinement.selected) :=
    fun coordinate =>
      (fiberSynchronization coordinate).restrictToHitParents
        (prepared.delta_pos.le.trans
          (prepared.strictScale
            (wz2PaperPreparedOneParentFineCoordinate
              prepared parent coordinate)).2.1)
        selection.refinement.selected
  let synchronization :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperPureInternalCoverSynchronization
          selection.refinement.selected.family
          (restricted.scaleData coordinate).coarse
          (restricted.scaleData coordinate).cover :=
    fun coordinate =>
      (selectedSynchronization coordinate).ofCoarseCoverHEq
        (restricted.coarse_eq coordinate).symm
        (restricted.cover_eq coordinate).symm
  have hSelectedCard :
      0 < selection.refinement.selected.family.card := by
    by_contra hzero
    have hselectedZero :
        selection.refinement.selected.family.enncard = 0 := by
      rw [Kakeya.Streamlined.TubeFamily.enncard]
      simp only [Nat.cast_eq_zero]
      omega
    have hcallerCard :
        0 <
          (wz2PaperPreparedOneParentFiber
            prepared parent).family.card := by
      change
        0 <
          (wz2PaperFullFiberIndices
            prepared.refinement.selected.family
            prepared.callerStrict.coarse parent).card
      exact Finset.card_pos.mpr
        (prepared.callerStrict.cover.fullFiber_nonempty parent)
    have hcallerENN :
        0 <
          (wz2PaperPreparedOneParentFiber
            prepared parent).family.enncard := by
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        (Nat.cast_pos.mpr hcallerCard :
          (0 : ENNReal) <
            ((wz2PaperPreparedOneParentFiber
              prepared parent).family.card : ENNReal))
    have hleft :
        0 <
          quantitative.weight *
            (wz2PaperPreparedOneParentFiber
              prepared parent).family.enncard :=
      ENNReal.mul_pos quantitative.weight_ne_zero hcallerENN.ne'
    have hretention := quantitative.global_retention
    rw [hselectedZero, mul_zero] at hretention
    exact (not_lt_of_ge hretention) hleft
  let hitCoarseNonempty :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        (((restricted.callerFiberData coordinate).scaleData.cover
          |>.hitParentSubfamily
            selection.refinement.selected)).family.Nonempty :=
    fun coordinate =>
      let sourceIndex :
          Fin selection.refinement.selected.family.card :=
        ⟨0, hSelectedCard⟩
      Fin.pos_iff_nonempty.mpr
        ⟨(restricted.callerFiberData coordinate).scaleData.cover
          |>.hitParent selection.refinement.selected sourceIndex⟩
  have selectedUniform :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        ∀ first second :
            Fin (((restricted.callerFiberData coordinate).scaleData.cover
              |>.hitParentSubfamily
                selection.refinement.selected)).family.card,
          wz2PaperFullFiberCount
              selection.refinement.selected.family
              (((restricted.callerFiberData coordinate).scaleData.cover
                |>.hitParentSubfamily
                  selection.refinement.selected)).family first ≤
            quantitative.selectedUniformConstant *
              wz2PaperFullFiberCount
                selection.refinement.selected.family
                (((restricted.callerFiberData coordinate).scaleData.cover
                  |>.hitParentSubfamily
                    selection.refinement.selected)).family second := by
    intro coordinate
    let branchHistorical :=
      selection.branch.callerFiberData
        (wz2PaperPreparedOneParentFineCoordinate
          prepared parent coordinate)
        (wz2PaperPreparedOneParentFineCoordinate_le
          prepared parent coordinate)
    exact
      selected_uniform_of_coarse_cover_heq
        selection.refinement.selected
        quantitative.selectedUniformConstant
        (callerFiberScaleData_coarse_eq
          branchHistorical
          (restricted.callerFiberData coordinate))
        (callerFiberScaleData_cover_eq
          branchHistorical
          (restricted.callerFiberData coordinate))
        (quantitative.selected_uniform coordinate)
  let rawPureScale :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperPureScaleCoverData
          selection.refinement.selected.family
          (prepared.strictScale
            (wz2PaperPreparedOneParentFineCoordinate
              prepared parent coordinate)).1
          (wz2PaperPreparedOneParentPureRestrictionConstant
            prepared parent selection quantitative) :=
    fun coordinate =>
      let pureData := callerFiberPureData coordinate
      pureData.pureScale.restrictToSynchronizedHitParents
        (restricted.callerFiberData coordinate).scaleData.coarse
        (pureData.coarse_eq.trans
          (callerFiberScaleData_coarse_eq
            pureData.historical
            (restricted.callerFiberData coordinate)))
        (restricted.callerFiberData coordinate).scaleData.cover
        (fiberSynchronization coordinate)
        selection.refinement.selected
        (hitCoarseNonempty coordinate)
        quantitative.weight_ne_zero
        quantitative.weight_ne_top
        quantitative.global_retention
        (selectedUniform coordinate)
  let pureScale :
      ∀ coordinate :
          Fin (wz2PaperPreparedOneParentFineScaleCount
            prepared parent),
        WZ2PaperPureScaleCoverData
          selection.refinement.selected.family
          (prepared.strictScale
            (wz2PaperPreparedOneParentFineCoordinate
              prepared parent coordinate)).1
          (wz2PaperPreparedOneParentPureScheduleConstant
            prepared parent selection quantitative restrictedConstant) :=
    fun coordinate =>
      (rawPureScale coordinate).mono
        (le_max_right
          restrictedConstant
          (wz2PaperPreparedOneParentPureRestrictionConstant
            prepared parent selection quantitative))
  refine
    {
      callerFiberPureData := callerFiberPureData
      synchronization := synchronization
      pureScale := pureScale
      coarse_eq := ?_
      cover_eq := ?_
    }
  · intro coordinate
    dsimp only [pureScale, WZ2PaperPureScaleCoverData.mono]
    exact
      (WZ2PaperPureScaleCoverData.restrictToSynchronizedHitParents_coarse
            (callerFiberPureData coordinate).pureScale
            (restricted.callerFiberData coordinate).scaleData.coarse
            ((callerFiberPureData coordinate).coarse_eq.trans
              (callerFiberScaleData_coarse_eq
                (callerFiberPureData coordinate).historical
                (restricted.callerFiberData coordinate)))
            (restricted.callerFiberData coordinate).scaleData.cover
            (fiberSynchronization coordinate)
            selection.refinement.selected
            (hitCoarseNonempty coordinate)
            quantitative.weight_ne_zero
            quantitative.weight_ne_top
            quantitative.global_retention
            (selectedUniform coordinate)).trans
        (restricted.coarse_eq coordinate).symm
  · intro coordinate
    exact proof_irrel_heq _ _

end WZ2PaperAlignedPureExactSource

end Kakeya.Assouad

end
