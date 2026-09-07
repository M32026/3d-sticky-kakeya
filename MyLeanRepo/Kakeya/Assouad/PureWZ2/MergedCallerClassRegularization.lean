import MyLeanRepo.Kakeya.Assouad.PureWZ2.AllCallerClassScheduleRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex
import Mathlib.Algebra.BigOperators.Fin

/-!
# Merge regularized caller classes with exact fiber provenance

Index the global selected family by the sigma type

`Σ caller, local selected tube in caller`.

The caller coordinate is therefore part of every global index.  Different
caller coordinates cannot collide because every local family is a union of
actual complete fibers in that caller's quotient class.  The resulting WZ
line cover has a definitionally transparent parent map, and each global full
caller fiber is exactly a finite reindexing of its local all-scale-CWA family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Local complete-parent regularizations indexed by an arbitrary caller
subfamily. -/
structure PureWZ2CallerSubfamilyRegularizationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerBase :
      Kakeya.Streamlined.TubeSubfamily quotient.callerCoarse)
    (coordinateCount : ℕ) where
  fiberData :
    ∀ parent : Fin callerBase.family.card,
      PureWZ2CallerClassRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient (callerBase.embedding parent) coordinateCount

/-- Generic merge over a caller subfamily. -/
structure PureWZ2GenericMergedCallerClassRegularizationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerBase :
      Kakeya.Streamlined.TubeSubfamily quotient.callerCoarse)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2CallerSubfamilyRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient callerBase coordinateCount)
    (sourceRetentionConstant : ENNReal) where
  merged : WZ2PaperPureTubeSubfamily fine
  indexEquiv :
    Fin merged.family.card ≃
      Σ parent : Fin callerBase.family.card,
        Fin (regularized.fiberData parent).complete.selectedFine.family.card
  ambient_embedding_eq :
    ∀ index,
      merged.embedding index =
        (regularized.fiberData
          (indexEquiv index).1).complete.selectedFine.embedding
            (indexEquiv index).2
  merged_nonempty : merged.family.Nonempty
  mergedShading : WZ1PaperTubeShading merged.family
  mergedShading_eq :
    mergedShading =
      restrictPaperShading merged.toTubeSubfamily shading
  mergedShading_mass_eq :
    mergedShading.mass =
      ∑ parent : Fin callerBase.family.card,
        (restrictPaperShading
          (regularized.fiberData
            parent).complete.selectedFine.toTubeSubfamily
          shading).mass
  selected_mass_retention :
    (∑ parent : Fin callerBase.family.card,
        quotient.callerActualWeight (callerBase.embedding parent)) ≤
      pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        mergedShading.mass
  source_mass_retention :
    shading.mass ≤
      sourceRetentionConstant *
        pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        mergedShading.mass
  callerCover :
    WZ1PaperTubeCover merged.family callerBase.family
  caller_parent_eq :
    ∀ index,
      callerCover.parent index = (indexEquiv index).1
  section6Cover :
    PureWZ2Section6Cover merged.family callerBase.family
  fiberIndexEquiv :
    ∀ parent : Fin callerBase.family.card,
      Fin (wz2PaperFullFiberIndices
        merged.family
        callerBase.family
        parent).card ≃
      Fin (regularized.fiberData parent).complete.selectedFine.family.card
  fiber_ambient_eq :
    ∀ parent : Fin callerBase.family.card,
      ∀ index :
        Fin (wz2PaperFullFiberIndices
          merged.family
          callerBase.family
          parent).card,
        merged.embedding
            ((wz2PaperFullFiberIndices
              merged.family
              callerBase.family
              parent).orderEmbOfFin rfl index) =
          (regularized.fiberData parent).complete.selectedFine.embedding
              (fiberIndexEquiv parent index)
  fiber_pure_cwa :
    ∀ parent : Fin callerBase.family.card,
      WZ2PaperPureCWAAtNearbyScales
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          merged.family
          (wz2PaperFullFiberIndices
            merged.family
            callerBase.family
            parent)).family
        outputConstant

theorem merge_caller_subfamily_regularizations
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (callerBase :
      Kakeya.Streamlined.TubeSubfamily quotient.callerCoarse)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2CallerSubfamilyRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient callerBase coordinateCount)
    (fineNonempty : fine.Nonempty)
    (callerBaseNonempty : callerBase.family.Nonempty)
    (sourceRetentionConstant : ENNReal)
    (sourceWeightRetention :
      shading.mass ≤
        sourceRetentionConstant *
          ∑ parent : Fin callerBase.family.card,
            quotient.callerActualWeight (callerBase.embedding parent)) :
    Nonempty
      (PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient callerBase coordinateCount regularized
        sourceRetentionConstant) := by
  let hitCaller := callerBase
  let Parent := Fin hitCaller.family.card
  let LocalFamily : Parent → Kakeya.Streamlined.TubeFamily delta :=
    fun parent =>
      (regularized.fiberData parent).complete.selectedFine.family
  let SigmaType := Σ parent : Parent, Fin (LocalFamily parent).card
  let totalCard := ∑ parent : Parent, (LocalFamily parent).card
  let indexEquiv : Fin totalCard ≃ SigmaType :=
    finSigmaFinEquiv.symm
  let ambientIndex : Fin totalCard → Fin fine.card :=
    fun index =>
      (regularized.fiberData
        (indexEquiv index).1).complete.selectedFine.embedding
          (indexEquiv index).2
  have ambientIndexInjective : Function.Injective ambientIndex := by
    intro first second hindex
    rcases hfirst : indexEquiv first with ⟨firstParent, firstLocal⟩
    rcases hsecond : indexEquiv second with ⟨secondParent, secondLocal⟩
    have firstAmbient :
        ambientIndex first =
          (regularized.fiberData firstParent).complete.selectedFine.embedding firstLocal := by
      dsimp only [ambientIndex]
      rw [hfirst]
    have secondAmbient :
        ambientIndex second =
          (regularized.fiberData secondParent).complete.selectedFine.embedding secondLocal := by
      dsimp only [ambientIndex]
      rw [hsecond]
    let firstActual :=
      actualNearby.scaleData.cover.parent
        ((regularized.fiberData firstParent).complete.selectedFine.embedding firstLocal)
    let secondActual :=
      actualNearby.scaleData.cover.parent
        ((regularized.fiberData secondParent).complete.selectedFine.embedding secondLocal)
    have firstActualMem :
        firstActual ∈
          (regularized.fiberData firstParent).selectedActualParents :=
      (regularized.fiberData firstParent).complete.selectedFine_parent_mem firstLocal
    have secondActualMem :
        secondActual ∈
          (regularized.fiberData secondParent).selectedActualParents :=
      (regularized.fiberData secondParent).complete.selectedFine_parent_mem secondLocal
    have firstClass :=
      (regularized.fiberData firstParent).selected_subset firstActualMem
    have secondClass :=
      (regularized.fiberData secondParent).selected_subset secondActualMem
    have actualEq : firstActual = secondActual := by
      dsimp only [firstActual, secondActual]
      exact congrArg actualNearby.scaleData.cover.parent <|
        firstAmbient.symm.trans (hindex.trans secondAmbient)
    have callerAmbientEq :
        hitCaller.embedding firstParent =
          hitCaller.embedding secondParent := by
      apply quotient.callerCenter.injective
      calc
        quotient.callerCenter (hitCaller.embedding firstParent) =
            quotient.net.center firstActual := by
          exact (Finset.mem_filter.mp firstClass).2.symm
        _ = quotient.net.center secondActual := by
          rw [actualEq]
        _ =
            quotient.callerCenter (hitCaller.embedding secondParent) := by
          exact (Finset.mem_filter.mp secondClass).2
    have parentEq : firstParent = secondParent :=
      hitCaller.embedding.injective callerAmbientEq
    subst secondParent
    have localEq : firstLocal = secondLocal := by
      apply
        (regularized.fiberData firstParent).complete.selectedFine.embedding.injective
      exact firstAmbient.symm.trans (hindex.trans secondAmbient)
    apply indexEquiv.injective
    rw [hfirst, hsecond, localEq]
  let merged : WZ2PaperPureTubeSubfamily fine :=
    {
      family :=
        {
          card := totalCard
          tube := fun index => fine.tube (ambientIndex index)
        }
      embedding :=
        {
          toFun := ambientIndex
          inj' := ambientIndexInjective
        }
      tube_eq := fun _ => rfl
    }
  have hitCallerNonempty : hitCaller.family.Nonempty :=
    callerBaseNonempty
  have mergedNonempty : merged.family.Nonempty := by
    let parent : Parent := ⟨0, hitCallerNonempty⟩
    have localNonempty :
        (LocalFamily parent).Nonempty :=
      (regularized.fiberData parent).selectedFine_nonempty
        fineNonempty
    let localIndex : Fin (LocalFamily parent).card :=
      ⟨0, localNonempty⟩
    exact
      Fin.pos_iff_nonempty.mpr
        ⟨indexEquiv.symm ⟨parent, localIndex⟩⟩
  let mergedShading :=
    restrictPaperShading merged.toTubeSubfamily shading
  have mergedMass :
      mergedShading.mass =
        ∑ parent : Parent,
          (restrictPaperShading
            (regularized.fiberData
              parent).complete.selectedFine.toTubeSubfamily
            shading).mass := by
    rw [restrictPaperShading_mass]
    change
      (∑ index : Fin merged.family.card,
          volume (shading.carrier (ambientIndex index))) =
        ∑ parent : Parent,
          (∑ localIndex :
              Fin (LocalFamily parent).card,
            volume
              (shading.carrier
                ((regularized.fiberData
                  parent).complete.selectedFine.embedding
                    localIndex)))
    let sigmaMass : SigmaType → ENNReal :=
      fun sigmaIndex =>
        volume
          (shading.carrier
            ((regularized.fiberData
              sigmaIndex.1).complete.selectedFine.embedding
                sigmaIndex.2))
    have globalToSigma :
        (∑ index : Fin merged.family.card,
          volume
            (shading.carrier
              (ambientIndex index))) =
          ∑ sigmaIndex : SigmaType,
            sigmaMass sigmaIndex := by
      exact
        Fintype.sum_equiv indexEquiv
          (fun index : Fin merged.family.card =>
            volume
              (shading.carrier
                (ambientIndex index)))
          sigmaMass
          (fun _ => rfl)
    rw [globalToSigma]
    rw [Fintype.sum_sigma]
  let commonLoss :=
    pureWZ2CompleteParentRegularizationLoss
      actualNearby.scaleData.coarse.card coordinateCount
  have localRetention :
      ∀ parent : Parent,
        quotient.callerActualWeight
            (hitCaller.embedding parent) ≤
          commonLoss *
            (restrictPaperShading
              (regularized.fiberData
                parent).complete.selectedFine.toTubeSubfamily
              shading).mass := by
    intro parent
    let localData := regularized.fiberData parent
    have retained := localData.retained_weight
    rw [localData.regularizationLoss_eq] at retained
    rw [localData.complete.restrictedShading_mass_eq
      shading actualNearby.scaleData.rho_pos.le]
    exact retained
  have selectedMassRetention :
      (∑ parent : Parent,
          quotient.callerActualWeight
            (hitCaller.embedding parent)) ≤
        commonLoss * mergedShading.mass := by
    rw [mergedMass]
    calc
      (∑ parent : Parent,
          quotient.callerActualWeight
            (hitCaller.embedding parent)) ≤
          ∑ parent : Parent,
            commonLoss *
              (restrictPaperShading
                (regularized.fiberData
                  parent).complete.selectedFine.toTubeSubfamily
                shading).mass := by
        apply Finset.sum_le_sum
        intro parent _
        exact localRetention parent
      _ =
          commonLoss *
            ∑ parent : Parent,
              (restrictPaperShading
                (regularized.fiberData
                  parent).complete.selectedFine.toTubeSubfamily
                shading).mass := by
        rw [Finset.mul_sum]
  have sourceMassRetention :
      shading.mass ≤
        sourceRetentionConstant * commonLoss * mergedShading.mass := by
    calc
      shading.mass ≤
          sourceRetentionConstant *
            ∑ parent : Parent,
              quotient.callerActualWeight
                (hitCaller.embedding parent) :=
        sourceWeightRetention
      _ ≤
          sourceRetentionConstant *
            (commonLoss * mergedShading.mass) := by
        gcongr
      _ =
          sourceRetentionConstant *
            commonLoss * mergedShading.mass := by
        ring
  let callerParent : Fin merged.family.card → Parent :=
    fun index => (indexEquiv index).1
  have callerParentSurjective : Function.Surjective callerParent := by
    intro parent
    have localNonempty :
        (LocalFamily parent).Nonempty :=
      (regularized.fiberData parent).selectedFine_nonempty
        fineNonempty
    let localIndex : Fin (LocalFamily parent).card :=
      ⟨0, localNonempty⟩
    refine ⟨indexEquiv.symm ⟨parent, localIndex⟩, ?_⟩
    change
      (indexEquiv
        (indexEquiv.symm ⟨parent, localIndex⟩)).1 =
        parent
    rw [indexEquiv.apply_symm_apply]
  have callerParentCovers :
      ∀ index,
        WZ1PaperTubeCovers
          (merged.family.tube index)
          (hitCaller.family.tube (callerParent index)) := by
    intro index
    let sigmaIndex := indexEquiv index
    let localData := regularized.fiberData sigmaIndex.1
    let ambientSource :=
      localData.complete.selectedFine.embedding sigmaIndex.2
    let actualParent :=
      actualNearby.scaleData.cover.parent ambientSource
    have actualMem :
        actualParent ∈ localData.selectedActualParents :=
      localData.complete.selectedFine_parent_mem sigmaIndex.2
    have classMem :=
      localData.selected_subset actualMem
    have centerEq :
        quotient.net.center actualParent =
          quotient.callerCenter
            (hitCaller.embedding sigmaIndex.1) :=
      (Finset.mem_filter.mp classMem).2
    have hcover :=
      quotient.caller_covers_of_actual_center
        ambientSource actualParent
        (hitCaller.embedding sigmaIndex.1)
        rfl centerEq
    change
      WZ1PaperTubeCovers
        (fine.tube (ambientIndex index))
        (hitCaller.family.tube (callerParent index))
    rw [hitCaller.tube_eq]
    simpa [ambientIndex, callerParent, sigmaIndex, localData,
      ambientSource] using hcover
  have callerCoarseDistinct :
      WZ1PaperIsEssentiallyDistinct hitCaller.family :=
    quotient.section6Cover.coarse_essentially_distinct.subfamily
      hitCaller
  let callerCover :
      WZ1PaperTubeCover merged.family hitCaller.family :=
    {
      parent := callerParent
      parent_surjective := callerParentSurjective
      parent_covers := callerParentCovers
      parent_unique := by
        intro source candidate candidateCovers
        by_contra hne
        have hseparated :=
          callerCoarseDistinct candidate (callerParent source) hne
        have htriangle :=
          wz1PaperLineDistance_triangle
            (hitCaller.family.tube candidate)
            (merged.family.tube source)
            (hitCaller.family.tube (callerParent source))
        have hsymmetry :
            wz1PaperLineDistance
                (hitCaller.family.tube candidate)
                (merged.family.tube source) =
              wz1PaperLineDistance
                (merged.family.tube source)
                (hitCaller.family.tube candidate) :=
          wz1PaperLineDistance_symm _ _
        rw [hsymmetry] at htriangle
        have assignedCovers := callerParentCovers source
        unfold WZ1PaperTubeCovers at candidateCovers assignedCovers
        exact
          (not_le_of_gt hseparated)
            (htriangle.trans (by linarith))
    }
  let mergedTubeSubfamily := merged.toTubeSubfamily
  let section6Cover :
      PureWZ2Section6Cover merged.family hitCaller.family :=
    {
      fine_line_class :=
        quotient.ambient_fine_line_class.subfamily
          mergedTubeSubfamily
      coarse_line_class :=
        quotient.section6Cover.coarse_line_class.subfamily
          hitCaller
      covers := fun source =>
        ⟨callerCover.parent source,
          callerCover.parent_covers source⟩
      parent_hit := by
        intro parent
        rcases callerCover.parent_surjective parent with
          ⟨source, hsource⟩
        refine ⟨source, ?_⟩
        rw [← hsource]
        exact callerCover.parent_covers source
      coarse_essentially_distinct := callerCoarseDistinct
    }
  have callerParentEq :
      ∀ index, callerCover.parent index = (indexEquiv index).1 :=
    fun _ => rfl
  have fiberPackage :
      ∀ parent : Parent,
        ∃ fiberEquiv :
            Fin (wz2PaperFullFiberIndices
              merged.family hitCaller.family parent).card ≃
              Fin (LocalFamily parent).card,
          (∀ index,
            merged.embedding
                ((wz2PaperFullFiberIndices
                  merged.family hitCaller.family parent)
                  |>.orderEmbOfFin rfl index) =
              (regularized.fiberData parent).complete.selectedFine.embedding
                  (fiberEquiv index)) ∧
          WZ2PaperPureCWAAtNearbyScales
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              merged.family
              (wz2PaperFullFiberIndices
                merged.family hitCaller.family parent)).family
            outputConstant := by
    intro parent
    let fiberSet :=
      wz2PaperFullFiberIndices
        merged.family hitCaller.family parent
    have fiberMem :
        ∀ index : Fin merged.family.card,
          index ∈ fiberSet ↔
            (indexEquiv index).1 = parent := by
      intro index
      rw [mem_wz2PaperFullFiberIndices_iff]
      constructor
      · intro hcover
        exact
          ((callerCover.parent_unique index parent hcover).trans
            (callerParentEq index)).symm
      · intro hparent
        rw [← hparent, ← callerParentEq index]
        exact callerCover.parent_covers index
    let sigmaFiber :=
      {index : SigmaType // index.1 = parent}
    let enumerationEquiv :
        Fin fiberSet.card ≃
          {index : Fin merged.family.card // index ∈ fiberSet} :=
      (fiberSet.orderIsoOfFin rfl).toEquiv
    let sigmaEquiv :
        {index : Fin merged.family.card // index ∈ fiberSet} ≃
          sigmaFiber :=
      {
        toFun := fun index =>
          ⟨indexEquiv index.1,
            (fiberMem index.1).mp index.2⟩
        invFun := fun index =>
          ⟨indexEquiv.symm index.1, by
            apply (fiberMem _).mpr
            simpa using index.2⟩
        left_inv := by
          intro index
          apply Subtype.ext
          exact indexEquiv.symm_apply_apply index.1
        right_inv := by
          intro index
          apply Subtype.ext
          exact indexEquiv.apply_symm_apply index.1
      }
    let localEquiv : sigmaFiber ≃ Fin (LocalFamily parent).card :=
      {
        toFun := fun index => index.2 ▸ index.1.2
        invFun := fun index => ⟨⟨parent, index⟩, rfl⟩
        left_inv := by
          intro index
          rcases index with ⟨value, property⟩
          rcases value with ⟨current, localIndex⟩
          cases property
          rfl
        right_inv := by
          intro index
          rfl
      }
    let fiberEquiv :=
      (enumerationEquiv.trans sigmaEquiv).trans localEquiv
    let ambientAt : SigmaType → Fin fine.card :=
      fun sigmaIndex =>
        (regularized.fiberData
          sigmaIndex.1).complete.selectedFine.embedding sigmaIndex.2
    have ambientEq :
        ∀ index,
          merged.embedding
              (fiberSet.orderEmbOfFin rfl index) =
            (regularized.fiberData parent).complete.selectedFine.embedding
                (fiberEquiv index) := by
      intro index
      let globalIndex := fiberSet.orderEmbOfFin rfl index
      have hparent :
          (indexEquiv globalIndex).1 = parent :=
        (fiberMem globalIndex).mp
          (Finset.orderEmbOfFin_mem fiberSet rfl index)
      have hsigma :
          sigmaEquiv (enumerationEquiv index) =
            ⟨indexEquiv globalIndex, hparent⟩ := by
        apply Subtype.ext
        rfl
      have hlocalBack :
          localEquiv.symm (fiberEquiv index) =
            sigmaEquiv (enumerationEquiv index) := by
        change
          localEquiv.symm
              (localEquiv (sigmaEquiv (enumerationEquiv index))) =
            sigmaEquiv (enumerationEquiv index)
        exact
          localEquiv.symm_apply_apply
            (sigmaEquiv (enumerationEquiv index))
      have hsigmaPair :
          (⟨parent, fiberEquiv index⟩ : SigmaType) =
            indexEquiv globalIndex := by
        calc
          (⟨parent, fiberEquiv index⟩ : SigmaType) =
              (localEquiv.symm (fiberEquiv index)).1 := rfl
          _ = (sigmaEquiv (enumerationEquiv index)).1 :=
            congrArg Subtype.val hlocalBack
          _ = indexEquiv globalIndex :=
            congrArg Subtype.val hsigma
      change
        ambientIndex globalIndex =
          (regularized.fiberData parent).complete.selectedFine.embedding
              (fiberEquiv index)
      change
        ambientAt (indexEquiv globalIndex) =
          ambientAt ⟨parent, fiberEquiv index⟩
      exact congrArg ambientAt hsigmaPair.symm
    let fiberFamily :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        merged.family fiberSet
    have tubeEq :
        ∀ index,
          fiberFamily.family.tube index =
            (LocalFamily parent).tube (fiberEquiv index) := by
      intro index
      rw [fiberFamily.tube_eq,
        merged.tube_eq,
        (regularized.fiberData parent).complete.selectedFine.tube_eq]
      exact congrArg fine.tube (ambientEq index)
    have fiberCWA :
        WZ2PaperPureCWAAtNearbyScales
          fiberFamily.family outputConstant :=
      (regularized.fiberData parent).pure_cwa.reindex
        fiberEquiv tubeEq
    exact ⟨fiberEquiv, ambientEq, fiberCWA⟩
  let fiberIndexEquiv :
      ∀ parent : Parent,
        Fin (wz2PaperFullFiberIndices
          merged.family hitCaller.family parent).card ≃
          Fin (LocalFamily parent).card :=
    fun parent => (fiberPackage parent).choose
  have fiberAmbientEq :
      ∀ parent : Parent,
        ∀ index :
          Fin (wz2PaperFullFiberIndices
            merged.family hitCaller.family parent).card,
          merged.embedding
              ((wz2PaperFullFiberIndices
                merged.family hitCaller.family parent)
                |>.orderEmbOfFin rfl index) =
            (regularized.fiberData parent).complete.selectedFine.embedding
                (fiberIndexEquiv parent index) :=
    fun parent => (fiberPackage parent).choose_spec.1
  have fiberCWA :
      ∀ parent : Parent,
        WZ2PaperPureCWAAtNearbyScales
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            merged.family
            (wz2PaperFullFiberIndices
              merged.family hitCaller.family parent)).family
          outputConstant :=
    fun parent => (fiberPackage parent).choose_spec.2
  exact
    ⟨{
      merged := merged
      indexEquiv := indexEquiv
      ambient_embedding_eq := fun index => rfl
      merged_nonempty := mergedNonempty
      mergedShading := mergedShading
      mergedShading_eq := rfl
      mergedShading_mass_eq := mergedMass
      selected_mass_retention := selectedMassRetention
      source_mass_retention := sourceMassRetention
      callerCover := callerCover
      caller_parent_eq := callerParentEq
      section6Cover := section6Cover
      fiberIndexEquiv := fiberIndexEquiv
      fiber_ambient_eq := fiberAmbientEq
      fiber_pure_cwa := fiberCWA
    }⟩

theorem restrictPaperShading_fromFinset_reindex_mass_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (merged localFamily : Kakeya.Streamlined.TubeSubfamily fine)
    (shading : WZ1PaperTubeShading fine)
    (indices : Finset (Fin merged.family.card))
    (reindex : Fin indices.card ≃ Fin localFamily.family.card)
    (ambient_eq :
      ∀ index,
        merged.embedding (indices.orderEmbOfFin rfl index) =
          localFamily.embedding (reindex index)) :
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        merged.family indices)
      (restrictPaperShading merged shading)).mass =
        (restrictPaperShading localFamily shading).mass := by
  rw [restrictPaperShading_fromFinset_mass]
  rw [restrictPaperShading_mass]
  rw [← Finset.sum_coe_sort indices
    (fun index =>
      volume ((restrictPaperShading merged shading).carrier index))]
  let enumeration :
      Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  let combined : indices ≃ Fin localFamily.family.card :=
    enumeration.symm.trans reindex
  change
    (∑ index : indices,
      volume (shading.carrier (merged.embedding index.1))) =
      ∑ index : Fin localFamily.family.card,
        volume (shading.carrier (localFamily.embedding index))
  exact
    Fintype.sum_equiv combined
      (fun index =>
        volume (shading.carrier (merged.embedding index.1)))
      (fun index =>
        volume (shading.carrier (localFamily.embedding index)))
      (fun index => by
        have ambient := ambient_eq (enumeration.symm index)
        have indexEq :
            indices.orderEmbOfFin rfl (enumeration.symm index) =
              index.1 :=
          congrArg Subtype.val
            (enumeration.apply_symm_apply index)
        rw [indexEq] at ambient
        simpa [combined] using
          congrArg
            (fun ambientIndex : Fin fine.card =>
              volume (shading.carrier ambientIndex))
            ambient)

theorem PureWZ2GenericMergedCallerClassRegularizationData.fiberShading_mass_eq_local
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {callerBase :
      Kakeya.Streamlined.TubeSubfamily quotient.callerCoarse}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2CallerSubfamilyRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient callerBase coordinateCount}
    {sourceRetentionConstant : ENNReal}
    (data :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient callerBase coordinateCount regularized
        sourceRetentionConstant)
    (parent : Fin callerBase.family.card) :
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        data.merged.family
        (wz2PaperFullFiberIndices
          data.merged.family callerBase.family parent))
      data.mergedShading).mass =
    (restrictPaperShading
      (regularized.fiberData
        parent).complete.selectedFine.toTubeSubfamily
      shading).mass := by
  rw [data.mergedShading_eq]
  exact
    restrictPaperShading_fromFinset_reindex_mass_eq
      data.merged.toTubeSubfamily
      (regularized.fiberData
        parent).complete.selectedFine.toTubeSubfamily
      shading
      (wz2PaperFullFiberIndices
        data.merged.family callerBase.family parent)
      (data.fiberIndexEquiv parent)
      (data.fiber_ambient_eq parent)

theorem PureWZ2GenericMergedCallerClassRegularizationData.fiber_mass_retention
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {callerBase :
      Kakeya.Streamlined.TubeSubfamily quotient.callerCoarse}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2CallerSubfamilyRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient callerBase coordinateCount}
    {sourceRetentionConstant : ENNReal}
    (data :
      PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient callerBase coordinateCount regularized
        sourceRetentionConstant)
    (parent : Fin callerBase.family.card) :
    quotient.callerActualWeight (callerBase.embedding parent) ≤
      pureWZ2CompleteParentRegularizationLoss
          actualNearby.scaleData.coarse.card coordinateCount *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            data.merged.family
            (wz2PaperFullFiberIndices
              data.merged.family callerBase.family parent))
          data.mergedShading).mass := by
  rw [data.fiberShading_mass_eq_local parent]
  have retained := (regularized.fiberData parent).retained_weight
  rw [(regularized.fiberData parent).regularizationLoss_eq] at retained
  rw [← (regularized.fiberData parent).complete.restrictedShading_mass_eq
    shading actualNearby.scaleData.rho_pos.le] at retained
  exact retained

/-- View the legacy all-positive package through the generic caller-subfamily
interface. -/
noncomputable def
    PureWZ2AllPositiveCallerRegularizationData.toCallerSubfamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount) :
    PureWZ2CallerSubfamilyRegularizationData
      (outputConstant := outputConstant)
      actualNearby quotient
      (quotient.callerCover.hitParentSubfamily
        quotient.positiveCallerFine)
      coordinateCount where
  fiberData := regularized.fiberData

/-- Compatibility alias for the legacy all-positive merged package. -/
abbrev PureWZ2MergedCallerClassRegularizationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount) :=
  PureWZ2GenericMergedCallerClassRegularizationData
    actualNearby quotient
    (quotient.callerCover.hitParentSubfamily
      quotient.positiveCallerFine)
    coordinateCount regularized.toCallerSubfamily
    (pureWZ2ParentQuotientNetConflictDegree : ENNReal)

/-- Legacy constructor, now a thin specialization of the generic merge. -/
theorem merge_caller_class_regularizations
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount)
    (fineNonempty : fine.Nonempty) :
    Nonempty
      (PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized) := by
  have callerBaseNonempty :
      (quotient.callerCover.hitParentSubfamily
        quotient.positiveCallerFine).family.Nonempty := by
    let source : Fin quotient.positiveCallerFine.family.card :=
      ⟨0, support.positiveFine_nonempty⟩
    exact
      Fin.pos_iff_nonempty.mpr
        ⟨quotient.callerCover.hitParent
          quotient.positiveCallerFine source⟩
  have sourceWeightRetention :
      shading.mass ≤
        (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          ∑ parent :
              Fin (quotient.callerCover.hitParentSubfamily
                quotient.positiveCallerFine).family.card,
            quotient.callerActualWeight
              ((quotient.callerCover.hitParentSubfamily
                quotient.positiveCallerFine).embedding parent) := by
    have positiveWeightSum :
      (∑ parent :
          Fin (quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).family.card,
        quotient.callerActualWeight
          ((quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).embedding parent)) =
          quotient.selectedShading.mass :=
      quotient.sum_positive_hitParent_weight
    rw [positiveWeightSum]
    exact quotient.retained_mass
  exact
    merge_caller_subfamily_regularizations
      actualNearby quotient
      (quotient.callerCover.hitParentSubfamily
        quotient.positiveCallerFine)
      coordinateCount regularized.toCallerSubfamily fineNonempty
      callerBaseNonempty
      (pureWZ2ParentQuotientNetConflictDegree : ENNReal)
      sourceWeightRetention

/-- View the preselected local regularizers through the generic interface. -/
noncomputable def
    PureWZ2PreselectedCallerRegularizationData.toCallerSubfamily
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {coordinateCount : ℕ}
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled}
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient coordinateCount preselection) :
    PureWZ2CallerSubfamilyRegularizationData
      (outputConstant := outputConstant)
      actualNearby quotient
      preselection.selectedCallerBase.toTubeSubfamily
      coordinateCount where
  fiberData := regularized.fiberData

/-- Selected-caller merge retaining both quotient and preselection losses. -/
theorem merge_preselected_caller_regularizations
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (coordinateCount : ℕ)
    (scales : Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (preselection :
      PureWZ2PostDeletionCallerWeightPreselectionData
        quotient coordinateCount scales scheduled)
    (regularized :
      PureWZ2PreselectedCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient coordinateCount preselection)
    (fineNonempty : fine.Nonempty) :
    Nonempty
      (PureWZ2GenericMergedCallerClassRegularizationData
        actualNearby quotient
        preselection.selectedCallerBase.toTubeSubfamily
        coordinateCount regularized.toCallerSubfamily
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant)) := by
  have sourceWeightRetention :
      shading.mass ≤
        ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
          preselection.retentionConstant) *
          ∑ parent : Fin preselection.selected.family.card,
            quotient.callerActualWeight
              ((pureWZ2PostDeletionPositiveCallerBase quotient).embedding
                (preselection.selected.embedding parent)) := by
    calc
      shading.mass ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            quotient.selectedShading.mass :=
        quotient.retained_mass
      _ =
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            ∑ parent :
                Fin (pureWZ2PostDeletionPositiveCallerBase
                  quotient).family.card,
              pureWZ2PostDeletionPositiveCallerWeight quotient parent := by
        rw [preselection.total_weight_eq]
      _ ≤
          (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            (preselection.retentionConstant *
              ∑ parent : Fin preselection.selected.family.card,
                pureWZ2PostDeletionPositiveCallerWeight quotient
                  (preselection.selected.embedding parent)) := by
        gcongr
        exact preselection.retained_weight
      _ =
          ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            preselection.retentionConstant) *
            ∑ parent : Fin preselection.selected.family.card,
              quotient.callerActualWeight
                ((pureWZ2PostDeletionPositiveCallerBase
                  quotient).embedding
                  (preselection.selected.embedding parent)) := by
        simp only [pureWZ2PostDeletionPositiveCallerWeight]
        ring
  exact
    merge_caller_subfamily_regularizations
      actualNearby quotient
      preselection.selectedCallerBase.toTubeSubfamily
      coordinateCount regularized.toCallerSubfamily fineNonempty
      preselection.selected_nonempty
      ((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
        preselection.retentionConstant)
      sourceWeightRetention

end Kakeya.Assouad

end
