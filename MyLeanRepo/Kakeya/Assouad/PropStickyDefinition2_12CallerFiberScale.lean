import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PreparedScaleRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerFiberScale

/-!
# Pure actual-John scale data on one complete caller fiber

For coordinates finer than the caller, the nested preparation proves that a
complete strict coordinate fiber lies wholly inside one caller fiber.  The
historical `callerFiber_scaleData` already constructs the restricted cover and
proves exact ambient full-fiber equality.  This module reuses that equality
to restrict the prepared pure actual-John witness with no cardinality loss.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- One complete caller fiber carrying pure scale data at a finer prepared
coordinate. -/
structure WZ2PaperCallerFiberPureScaleData
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
    (callerParent : Fin prepared.callerStrict.coarse.card)
    (coordinate : Fin prepared.strictScaleCount) where
  historical :
    WZ2PaperCallerFiberScaleData
      prepared callerParent coordinate
  pureScale :
    WZ2PaperPureScaleCoverData
      (prepared.callerStrict.cover.fullFiberSubfamily
        callerParent).family
      (prepared.strictScale coordinate).1
      prepared.structuralConstant
  coarse_eq :
    pureScale.coarse = historical.scaleData.coarse
  cover_eq :
    HEq pureScale.cover
      (historical.synchronization
        (fun rho =>
          aligned.canonicalSynchronizationFor prepared rho)).publicCover

namespace WZ2PaperCallerFiberScaleData

/-- The restricted coarse family as an actual subfamily of the prepared
coordinate coarse family. -/
def coarseSubfamily
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
    {callerParent : Fin prepared.callerStrict.coarse.card}
    {coordinate : Fin prepared.strictScaleCount}
    (data :
      WZ2PaperCallerFiberScaleData
        prepared callerParent coordinate) :
    Kakeya.Streamlined.TubeSubfamily
      (prepared.strictScaleData coordinate).coarse where
  family := data.scaleData.coarse
  embedding := ⟨data.ambientParent, data.ambientParent_injective⟩
  tube_eq := data.ambientParent_tube_eq

end WZ2PaperCallerFiberScaleData

namespace WZ2PaperAlignedPureExactSource

/-- Convert one historical complete-fiber equality from line fibers to public
ordinary strict fibers using the retained synchronization. -/
theorem callerFiber_complete_ordinary
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
    (callerParent : Fin prepared.callerStrict.coarse.card)
    (coordinate : Fin prepared.strictScaleCount)
    (historical :
      WZ2PaperCallerFiberScaleData
        prepared callerParent coordinate)
    (parent : Fin historical.scaleData.coarse.card) :
    Finset.image
        (prepared.callerStrict.cover.fullFiberSubfamily
          callerParent).embedding
        (wz2PaperOrdinaryFullFiberIndices
          (prepared.callerStrict.cover.fullFiberSubfamily
            callerParent).family
          historical.scaleData.coarse parent) =
      wz2PaperOrdinaryFullFiberIndices
        prepared.refinement.selected.family
        (prepared.strictScaleData coordinate).coarse
        (historical.ambientParent parent) := by
  let canonicalSynchronization :=
    aligned.canonicalSynchronizationFor prepared
  let fiberSync :=
    historical.synchronization canonicalSynchronization
  have hambient :
      wz2PaperOrdinaryFullFiberIndices
          prepared.refinement.selected.family
          (prepared.strictScaleData coordinate).coarse
          (historical.ambientParent parent) =
        wz2PaperFullFiberIndices
          prepared.refinement.selected.family
          (prepared.strictScaleData coordinate).coarse
          (historical.ambientParent parent) :=
    (prepared.strict_synchronization
      canonicalSynchronization coordinate)
      |>.ordinaryFullFiberIndices_eq_internalFullFiber
      (prepared.delta_pos.le.trans
        (prepared.strictScale coordinate).2.1)
      (historical.ambientParent parent)
  have hlocal :
      wz2PaperOrdinaryFullFiberIndices
          (prepared.callerStrict.cover.fullFiberSubfamily
            callerParent).family
          historical.scaleData.coarse parent =
        wz2PaperFullFiberIndices
          (prepared.callerStrict.cover.fullFiberSubfamily
            callerParent).family
          historical.scaleData.coarse parent :=
    fiberSync.ordinaryFullFiberIndices_eq_internalFullFiber
      (prepared.delta_pos.le.trans
        (prepared.strictScale coordinate).2.1)
      parent
  rw [hlocal, hambient]
  exact historical.full_fiber_complete parent

/-- Transport a pure subfamily across an equality of ambient families. -/
private noncomputable def pureSubfamilyOfEq
    {rho : ℝ}
    {first second : Kakeya.Streamlined.TubeFamily rho}
    (selected : Kakeya.Streamlined.TubeSubfamily first)
    (hambient : first = second) :
    WZ2PaperPureTubeSubfamily second where
  family := selected.family
  embedding :=
    selected.embedding.trans
      (Equiv.cast
        (congrArg
          (fun family : Kakeya.Streamlined.TubeFamily rho =>
            Fin family.card)
          hambient)).toEmbedding
  tube_eq := by
    subst second
    intro index
    simpa using selected.tube_eq index

/-- Restrict one prepared pure scale witness to a complete caller fiber. -/
noncomputable def callerFiberScaleData
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
    (callerParent : Fin prepared.callerStrict.coarse.card)
    (coordinate : Fin prepared.strictScaleCount)
    (hfine : prepared.callerLevel.val ≤ coordinate.val) :
    WZ2PaperCallerFiberPureScaleData
      aligned prepared callerParent coordinate := by
  let ambientPure :=
    aligned.preparedScaleData prepared coordinate
  let historical :=
    Classical.choice
      (prepared.callerFiber_scaleData
        callerParent coordinate hfine)
  let callerFiber :=
    prepared.callerStrict.cover.fullFiberSubfamily callerParent
  let selectedFine :=
    WZ2PaperPureTubeSubfamily.ofTubeSubfamily callerFiber
  let coarseSubfamily := historical.coarseSubfamily
  have hambientCoarse :
      (prepared.strictScaleData coordinate).coarse =
        ambientPure.pureScale.coarse :=
    ambientPure.coarse_eq.symm
  let selectedCoarse :=
    pureSubfamilyOfEq coarseSubfamily hambientCoarse
  let canonicalSynchronization :=
    aligned.canonicalSynchronizationFor prepared
  let fiberSync :=
    historical.synchronization canonicalSynchronization
  have hcover :
      WZ2PaperPurePartitioningCover
        callerFiber.family selectedCoarse.family := by
    simpa [callerFiber, selectedCoarse, pureSubfamilyOfEq,
      coarseSubfamily,
      WZ2PaperCallerFiberScaleData.coarseSubfamily,
      hambientCoarse] using
        fiberSync.publicCover
  have huniform :
      WZ2PaperPureFullFibersAreCUniform
        callerFiber.family selectedCoarse.family
        prepared.structuralConstant := by
    simpa [callerFiber, selectedCoarse, pureSubfamilyOfEq,
      coarseSubfamily,
      WZ2PaperCallerFiberScaleData.coarseSubfamily,
      hambientCoarse] using
        fiberSync.public_full_fiber_uniform
          (prepared.delta_pos.le.trans
            (prepared.strictScale coordinate).2.1)
          historical.scaleData.full_fiber_uniform
  have himage :
      ∀ parent : Fin selectedCoarse.family.card,
        Finset.image selectedFine.embedding
            (wz2PaperOrdinaryFullFiberIndices
              selectedFine.family selectedCoarse.family parent) =
          wz2PaperOrdinaryFullFiberIndices
            prepared.refinement.selected.family
            ambientPure.pureScale.coarse
            (selectedCoarse.embedding parent) := by
    intro parent
    let localParent : Fin historical.scaleData.coarse.card :=
      ⟨parent.1, by
        simpa [selectedCoarse, pureSubfamilyOfEq,
          coarseSubfamily,
          WZ2PaperCallerFiberScaleData.coarseSubfamily] using
            parent.2⟩
    have hsource :=
      aligned.callerFiber_complete_ordinary
        prepared callerParent coordinate historical localParent
    have hleft :
        Finset.image selectedFine.embedding
            (wz2PaperOrdinaryFullFiberIndices
              selectedFine.family selectedCoarse.family parent) =
          Finset.image callerFiber.embedding
            (wz2PaperOrdinaryFullFiberIndices
              callerFiber.family historical.scaleData.coarse
              localParent) := by
      ext ambientSource
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨localSource, hlocal, rfl⟩
        refine ⟨localSource, ?_, ?_⟩
        · change
            localSource ∈
              wz2PaperOrdinaryFullFiberIndices
                callerFiber.family historical.scaleData.coarse
                localParent at hlocal ⊢
          exact hlocal
        · rfl
      · rintro ⟨localSource, hlocal, rfl⟩
        refine ⟨localSource, ?_, ?_⟩
        · change
            localSource ∈
              wz2PaperOrdinaryFullFiberIndices
                callerFiber.family historical.scaleData.coarse
                localParent at hlocal ⊢
          exact hlocal
        · rfl
    have hcoarseTube :
        ambientPure.pureScale.coarse.tube
            (selectedCoarse.embedding parent) =
          (prepared.strictScaleData coordinate).coarse.tube
            (historical.ambientParent localParent) := by
      exact
        (selectedCoarse.tube_eq parent).symm.trans
          (historical.ambientParent_tube_eq localParent)
    have hright :
        wz2PaperOrdinaryFullFiberIndices
            prepared.refinement.selected.family
            (prepared.strictScaleData coordinate).coarse
            (historical.ambientParent localParent) =
          wz2PaperOrdinaryFullFiberIndices
            prepared.refinement.selected.family
            ambientPure.pureScale.coarse
            (selectedCoarse.embedding parent) := by
      ext ambientSource
      simp only [mem_wz2PaperOrdinaryFullFiberIndices_iff]
      rw [hcoarseTube]
    exact hleft.trans (hsource.trans hright)
  have hratio :
      ∀ parent : Fin selectedCoarse.family.card,
        wz2PaperOrdinaryFullFiberCount
            prepared.refinement.selected.family
            ambientPure.pureScale.coarse
            (selectedCoarse.embedding parent) ≤
          (1 : ENNReal) *
            wz2PaperOrdinaryFullFiberCount
              selectedFine.family selectedCoarse.family parent := by
    intro parent
    rw [wz2PaperOrdinaryFullFiberCount,
      wz2PaperOrdinaryFullFiberCount, one_mul]
    have hcard := congrArg Finset.card (himage parent)
    rw [Finset.card_image_of_injective _
      selectedFine.embedding.injective] at hcard
    exact_mod_cast hcard.symm.le
  let pureScale :=
    ambientPure.pureScale.restrict
      selectedFine selectedCoarse hcover huniform
      hratio
  refine
    {
      historical := historical
      pureScale := pureScale.mono (by
        simp [pureScale])
      coarse_eq := ?_
      cover_eq := ?_
    }
  · dsimp only [WZ2PaperPureScaleCoverData.mono]
    dsimp only [pureScale, WZ2PaperPureScaleCoverData.restrict]
    rfl
  · exact proof_irrel_heq _ _

end WZ2PaperAlignedPureExactSource

end Kakeya.Assouad

end
