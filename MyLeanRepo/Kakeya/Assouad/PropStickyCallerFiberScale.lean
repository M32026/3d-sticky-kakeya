import MyLeanRepo.Kakeya.Assouad.PropStickyCallerFiberScaleStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyCallerFiberUniformity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-! # Exact strict-scale witnesses on one complete caller fiber -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem parent_eq_of_scale_data_heq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceScale targetScale :
      Kakeya.Streamlined.AdmissibleScale delta}
    {C : ENNReal}
    {sourceData :
      WZ2PaperScaleCoverData family sourceScale C}
    {targetData :
      WZ2PaperScaleCoverData family targetScale C}
    (hscale : sourceScale = targetScale)
    (hdata : HEq sourceData targetData)
    {first second : Fin family.card}
    (hparent :
      sourceData.cover.parent first =
        sourceData.cover.parent second) :
    targetData.cover.parent first =
      targetData.cover.parent second := by
  subst targetScale
  have hdataEq : sourceData = targetData :=
    eq_of_heq hdata
  rwa [← hdataEq]

theorem
    WZ2PaperCallerStrictPreparationData.callerFiber_scaleData
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
    (callerParent : Fin prepared.callerStrict.coarse.card)
    (coordinate : Fin prepared.strictScaleCount)
    (hfine : prepared.callerLevel.val ≤ coordinate.val) :
    Nonempty
      (WZ2PaperCallerFiberScaleData
        prepared callerParent coordinate) := by
  let fine := prepared.refinement.selected.family
  let callerFiber :=
    prepared.callerStrict.cover.fullFiberSubfamily callerParent
  let ambientData := prepared.strictScaleData coordinate
  let hitCoarse :=
    ambientData.cover.hitParentSubfamily callerFiber
  let restrictedCover :=
    ambientData.cover.restrictToHitParents callerFiber
  have hLine :
      WZ1PaperIsLineClass hitCoarse.family :=
    ambientData.coarse_line_class.subfamily hitCoarse
  have hDistinct :
      WZ1PaperIsEssentiallyDistinct hitCoarse.family :=
    ambientData.coarse_essentially_distinct.subfamily hitCoarse
  have hUniform :
      ∀ first second : Fin hitCoarse.family.card,
        wz2PaperFullFiberCount
            callerFiber.family hitCoarse.family first ≤
          prepared.structuralConstant *
            wz2PaperFullFiberCount
              callerFiber.family hitCoarse.family second :=
    prepared.callerFiber_strict_uniform
      callerParent coordinate
  have hComplete :
      ∀ parent : Fin hitCoarse.family.card,
        Finset.image callerFiber.embedding
            (wz2PaperFullFiberIndices
              callerFiber.family hitCoarse.family parent) =
          wz2PaperFullFiberIndices
            fine ambientData.coarse (hitCoarse.embedding parent) := by
    intro parent
    apply Finset.ext
    intro ambientSource
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨localSource, hlocalSource, rfl⟩
      have hlocalParent :
          restrictedCover.parent localSource = parent :=
        (restrictedCover.mem_fullFiber_iff_parent
          parent localSource).mp hlocalSource
      have hambientParent :
          ambientData.cover.parent
              (callerFiber.embedding localSource) =
            hitCoarse.embedding parent := by
        calc
          ambientData.cover.parent
                (callerFiber.embedding localSource) =
              hitCoarse.embedding
                (ambientData.cover.hitParent
                  callerFiber localSource) :=
            (ambientData.cover.hitParent_ambient
              callerFiber localSource).symm
          _ = hitCoarse.embedding parent :=
            congrArg hitCoarse.embedding hlocalParent
      exact
        (ambientData.cover.mem_fullFiber_iff_parent
          (hitCoarse.embedding parent)
          (callerFiber.embedding localSource)).mpr hambientParent
    · intro hambient
      have hambientParent :
          ambientData.cover.parent ambientSource =
            hitCoarse.embedding parent :=
        (ambientData.cover.mem_fullFiber_iff_parent
          (hitCoarse.embedding parent) ambientSource).mp hambient
      rcases ambientData.cover.hitParent_surjective callerFiber parent with
        ⟨reference, hreference⟩
      have hreferenceParent :
          ambientData.cover.parent
              (callerFiber.embedding reference) =
            hitCoarse.embedding parent := by
        have h := congrArg hitCoarse.embedding hreference
        rw [ambientData.cover.hitParent_ambient] at h
        exact h
      have hsameStrict :
          ambientData.cover.parent ambientSource =
            ambientData.cover.parent
              (callerFiber.embedding reference) := by
        rw [hambientParent, hreferenceParent]
      have hsameCaller :=
        prepared.parent_nested_of_le
          prepared.callerLevel coordinate hfine
          ambientSource (callerFiber.embedding reference)
          hsameStrict
      have hsameCaller' :
          prepared.callerStrict.cover.parent ambientSource =
            prepared.callerStrict.cover.parent
              (callerFiber.embedding reference) := by
        exact
          parent_eq_of_scale_data_heq
            prepared.callerScale_eq
            prepared.callerScaleData_eq hsameCaller
      have hreferenceCaller :
          prepared.callerStrict.cover.parent
              (callerFiber.embedding reference) =
            callerParent :=
        (prepared.callerStrict.cover.mem_fullFiber_iff_parent
          callerParent _).mp
          (prepared.callerStrict.cover.fullFiberSubfamily_mem
            callerParent reference)
      rw [hreferenceCaller] at hsameCaller'
      have hambientCaller :
          ambientSource ∈
            wz2PaperFullFiberIndices
              fine prepared.callerStrict.coarse callerParent :=
        (prepared.callerStrict.cover.mem_fullFiber_iff_parent
          callerParent ambientSource).mpr hsameCaller'
      let localSource : Fin callerFiber.family.card :=
        ((wz2PaperFullFiberIndices
          fine prepared.callerStrict.coarse callerParent)
          |>.orderIsoOfFin rfl).symm
            ⟨ambientSource, hambientCaller⟩
      have hlocalAmbient :
          callerFiber.embedding localSource = ambientSource := by
        exact congrArg Subtype.val
          (((wz2PaperFullFiberIndices
            fine prepared.callerStrict.coarse callerParent)
            |>.orderIsoOfFin rfl).apply_symm_apply
              ⟨ambientSource, hambientCaller⟩)
      refine Finset.mem_image.mpr ⟨localSource, ?_, hlocalAmbient⟩
      apply
        (restrictedCover.mem_fullFiber_iff_parent
          parent localSource).mpr
      apply hitCoarse.embedding.injective
      calc
        hitCoarse.embedding
              (restrictedCover.parent localSource) =
            ambientData.cover.parent
              (callerFiber.embedding localSource) :=
          ambientData.cover.hitParent_ambient
            callerFiber localSource
        _ = ambientData.cover.parent ambientSource := by
          rw [hlocalAmbient]
        _ = hitCoarse.embedding parent :=
          hambientParent
  have hRescaled :
      ∀ parent : Fin hitCoarse.family.card,
        Nonempty
          (WZ2PaperUnitRescaledFamilyData
            restrictedCover parent ambientData.rho_pos
            prepared.structuralConstant) := by
    intro parent
    let ambientParent := hitCoarse.embedding parent
    rcases ambientData.rescaledFiber ambientParent with
      ⟨ambientFiber⟩
    rcases
        wz2_paper_complete_fiber_reindex
          ambientData.cover callerFiber restrictedCover
          parent ambientParent (hComplete parent)
      with ⟨reindex⟩
    let localEquiv :
        Fin (restrictedCover.fullFiberSubfamily parent).family.card ≃
          Fin (ambientData.cover.fullFiberSubfamily
            ambientParent).family.card :=
      Equiv.ofBijective reindex.localIndex
        reindex.localIndex_bijective
    let ambientEquiv :=
      ambientFiber.targetEquivFullFiber
    let targetToLocal :
        Fin ambientFiber.targetFamily.card →
          Fin (restrictedCover.fullFiberSubfamily parent).family.card :=
      fun target =>
        localEquiv.symm (ambientEquiv target)
    have hTargetToLocalBijective :
        Function.Bijective targetToLocal :=
      (ambientEquiv.trans localEquiv.symm).bijective
    let sourceIndex :
        Fin ambientFiber.targetFamily.card →
          Fin callerFiber.family.card :=
      fun target =>
        (restrictedCover.fullFiberSubfamily parent).embedding
          (targetToLocal target)
    have hSourceIndexMem :
        ∀ target,
          sourceIndex target ∈
            wz2PaperFullFiberIndices
              callerFiber.family hitCoarse.family parent := by
      intro target
      exact
        restrictedCover.fullFiberSubfamily_mem
          parent (targetToLocal target)
    have hSourceIndexInjective :
        Function.Injective sourceIndex :=
      (restrictedCover.fullFiberSubfamily parent).embedding.injective.comp
        hTargetToLocalBijective.injective
    have hSourceIndexSurjective :
        ∀ sourceIndexCandidate,
          sourceIndexCandidate ∈
              wz2PaperFullFiberIndices
                callerFiber.family hitCoarse.family parent →
            ∃ target, sourceIndex target = sourceIndexCandidate := by
      intro sourceIndexCandidate hsource
      let localIndex :
          Fin (restrictedCover.fullFiberSubfamily parent).family.card :=
        ((wz2PaperFullFiberIndices
          callerFiber.family hitCoarse.family parent)
          |>.orderIsoOfFin rfl).symm
            ⟨sourceIndexCandidate, hsource⟩
      have hLocalEmbedding :
          (restrictedCover.fullFiberSubfamily parent).embedding
              localIndex =
            sourceIndexCandidate := by
        exact congrArg Subtype.val
          (((wz2PaperFullFiberIndices
            callerFiber.family hitCoarse.family parent)
            |>.orderIsoOfFin rfl).apply_symm_apply
              ⟨sourceIndexCandidate, hsource⟩)
      rcases hTargetToLocalBijective.surjective localIndex with
        ⟨target, htarget⟩
      refine ⟨target, ?_⟩
      dsimp only [sourceIndex]
      rw [htarget, hLocalEmbedding]
    have hAxis :
        ∀ target,
          tubeAxisLine (ambientFiber.targetFamily.tube target) =
            wz1PaperUnitRescalingMap
                (hitCoarse.family.tube parent)
                ambientData.rho_pos ''
              tubeAxisLine
                (callerFiber.family.tube
                  (sourceIndex target)) := by
      intro target
      have hAmbientAxis := ambientFiber.target_axis target
      have hAmbientEq :
          callerFiber.embedding (sourceIndex target) =
            ambientFiber.sourceIndex target := by
        calc
          callerFiber.embedding
              ((restrictedCover.fullFiberSubfamily parent).embedding
                (targetToLocal target)) =
              (ambientData.cover.fullFiberSubfamily
                ambientParent).embedding
                (localEquiv (targetToLocal target)) := by
            exact reindex.ambient_eq _
          _ =
              (ambientData.cover.fullFiberSubfamily
                ambientParent).embedding
                (ambientEquiv target) := by
            rw [localEquiv.apply_symm_apply]
          _ = ambientFiber.sourceIndex target :=
            ambientFiber.targetEquivFullFiber_ambient target
      rw [hitCoarse.tube_eq]
      rw [hAmbientAxis]
      congr 2
      rw [callerFiber.tube_eq]
      exact congrArg fine.tube hAmbientEq.symm
    exact
      ⟨{
        targetFamily := ambientFiber.targetFamily
        sourceIndex := sourceIndex
        sourceIndex_mem := hSourceIndexMem
        sourceIndex_injective := hSourceIndexInjective
        sourceIndex_surjective := hSourceIndexSurjective
        target_axis := hAxis
        target_line_class := ambientFiber.target_line_class
        convex_wolff := ambientFiber.convex_wolff
      }⟩
  let scaleData :
      WZ2PaperScaleCoverData
        callerFiber.family
        (prepared.strictScale coordinate)
        prepared.structuralConstant :=
    {
      rho_pos := ambientData.rho_pos
      coarse := hitCoarse.family
      cover := restrictedCover
      coarse_line_class := hLine
      coarse_essentially_distinct := hDistinct
      full_fiber_uniform := hUniform
      rescaledFiber := hRescaled
    }
  exact
    ⟨{
      scaleData := scaleData
      coarse_eq := rfl
      cover_eq := HEq.rfl
      synchronization := by
        intro canonicalSynchronization
        let selectedSync :=
          prepared.strict_synchronization
            canonicalSynchronization coordinate
        exact
          selectedSync.restrictToHitParents
            (prepared.delta_pos.le.trans
              (prepared.strictScale coordinate).2.1)
            callerFiber
      ambientParent := hitCoarse.embedding
      ambientParent_injective := hitCoarse.embedding.injective
      ambientParent_tube_eq := hitCoarse.tube_eq
      parent_ambient_eq := by
        intro sourceIndex
        exact
          ambientData.cover.hitParent_ambient
            callerFiber sourceIndex
      full_fiber_complete := hComplete
      coarse_strongly_separated := by
        intro first second hne
        have hambientNe :
            hitCoarse.embedding first ≠
              hitCoarse.embedding second :=
          hitCoarse.embedding.injective.ne hne
        change
          wz2PaperLiteralSourceSeparationFactor * (prepared.strictScale coordinate).1 <
            wz1PaperLineDistance
              (hitCoarse.family.tube first)
              (hitCoarse.family.tube second)
        simpa only [hitCoarse.tube_eq] using
          prepared.strict_hit_parent_separated coordinate
            (hitCoarse.embedding first)
            (hitCoarse.embedding second) hambientNe
    }⟩

end Kakeya.Assouad

end
