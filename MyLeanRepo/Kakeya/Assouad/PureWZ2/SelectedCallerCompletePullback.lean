import MyLeanRepo.Kakeya.Assouad.PureWZ2.MergedCallerClassRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex

/-!
# Complete pullback of a selected caller family

After all caller fibers have been regularized and merged, select caller
parents and retain every member of each selected complete WZ caller fiber.
The resulting fine/coarse configuration is the common family on which the
coarse pure CWA, balancing, and final fiber conclusions must be stated.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2SelectedCallerCompletePullbackData
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
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount}
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (selectedCoarse :
      WZ2PaperPureTubeSubfamily
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family) where
  selectedFineIndices : Finset (Fin merged.merged.family.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        ∃ parent : Fin selectedCoarse.family.card,
          merged.callerCover.parent source =
            selectedCoarse.embedding parent
  selectedFine :
    Kakeya.Streamlined.TubeSubfamily merged.merged.family
  selectedFine_eq :
    selectedFine =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        merged.merged.family selectedFineIndices
  selectedFineShading :
    WZ1PaperTubeShading selectedFine.family
  selectedFineShading_eq :
    selectedFineShading =
      restrictPaperShading selectedFine merged.mergedShading
  callerCover :
    WZ1PaperTubeCover selectedFine.family selectedCoarse.family
  section6Cover :
    PureWZ2Section6Cover selectedFine.family selectedCoarse.family
  parent_ambient_eq :
    ∀ source,
      selectedCoarse.embedding (callerCover.parent source) =
        merged.callerCover.parent (selectedFine.embedding source)
  full_fiber_complete :
    ∀ parent : Fin selectedCoarse.family.card,
      Finset.image selectedFine.embedding
          (wz2PaperFullFiberIndices
            selectedFine.family selectedCoarse.family parent) =
        wz2PaperFullFiberIndices
          merged.merged.family
          (quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).family
          (selectedCoarse.embedding parent)
  fiber_pure_cwa :
    ∀ parent : Fin selectedCoarse.family.card,
      WZ2PaperPureCWAAtNearbyScales
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          selectedFine.family
          (wz2PaperFullFiberIndices
            selectedFine.family selectedCoarse.family parent)).family
        outputConstant

/-- Retain exactly the complete merged fibers of the selected callers. -/
theorem pureWZ2_selected_caller_complete_pullback
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
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount}
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (selectedCoarse :
      WZ2PaperPureTubeSubfamily
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family)
    (selectedCoarseNonempty : selectedCoarse.family.Nonempty) :
    Nonempty
      (PureWZ2SelectedCallerCompletePullbackData
        merged selectedCoarse) := by
  let ambientCoarse :=
    (quotient.callerCover.hitParentSubfamily
      quotient.positiveCallerFine).family
  let selectedFineIndices : Finset (Fin merged.merged.family.card) :=
    Finset.univ.filter fun source =>
      ∃ parent : Fin selectedCoarse.family.card,
        merged.callerCover.parent source =
          selectedCoarse.embedding parent
  let selectedFine :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      merged.merged.family selectedFineIndices
  let selectedFineShading :=
    restrictPaperShading selectedFine merged.mergedShading
  have selectedEmbeddingMem :
      ∀ source : Fin selectedFine.family.card,
        selectedFine.embedding source ∈ selectedFineIndices :=
    fun source =>
      Finset.orderEmbOfFin_mem selectedFineIndices rfl source
  have parentExists :
      ∀ source : Fin selectedFine.family.card,
        ∃ parent : Fin selectedCoarse.family.card,
          merged.callerCover.parent
              (selectedFine.embedding source) =
            selectedCoarse.embedding parent := by
    intro source
    exact (Finset.mem_filter.mp (selectedEmbeddingMem source)).2
  let parent :
      Fin selectedFine.family.card →
        Fin selectedCoarse.family.card :=
    fun source => Classical.choose (parentExists source)
  have parentAmbient :
      ∀ source,
        selectedCoarse.embedding (parent source) =
          merged.callerCover.parent
            (selectedFine.embedding source) := by
    intro source
    exact (Classical.choose_spec (parentExists source)).symm
  have selectedAmbientSurjective :
      ∀ source ∈ selectedFineIndices,
        ∃ selectedSource : Fin selectedFine.family.card,
          selectedFine.embedding selectedSource = source := by
    intro source hsource
    let member : selectedFineIndices := ⟨source, hsource⟩
    let selectedSource : Fin selectedFine.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm member
    exact
      ⟨selectedSource,
        congrArg Subtype.val
          (selectedFineIndices.orderIsoOfFin rfl
            |>.apply_symm_apply member)⟩
  have parentSurjective : Function.Surjective parent := by
    intro selectedParent
    let ambientParent := selectedCoarse.embedding selectedParent
    rcases merged.callerCover.parent_surjective ambientParent with
      ⟨ambientSource, hsourceParent⟩
    have sourceSelected : ambientSource ∈ selectedFineIndices := by
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ ambientSource,
            ⟨selectedParent, hsourceParent⟩⟩
    rcases selectedAmbientSurjective ambientSource sourceSelected with
      ⟨source, hsource⟩
    refine ⟨source, ?_⟩
    apply selectedCoarse.embedding.injective
    rw [parentAmbient, hsource, hsourceParent]
  let callerCover :
      WZ1PaperTubeCover selectedFine.family selectedCoarse.family :=
    {
      parent := parent
      parent_surjective := parentSurjective
      parent_covers := by
        intro source
        rw [selectedFine.tube_eq, selectedCoarse.tube_eq,
          parentAmbient]
        exact
          merged.callerCover.parent_covers
            (selectedFine.embedding source)
      parent_unique := by
        intro source candidate hcovered
        apply selectedCoarse.embedding.injective
        rw [parentAmbient]
        apply
          merged.callerCover.parent_unique
            (selectedFine.embedding source)
        rw [← selectedFine.tube_eq source,
          ← selectedCoarse.tube_eq candidate]
        exact hcovered
    }
  have fullFiberComplete :
      ∀ selectedParent : Fin selectedCoarse.family.card,
        Finset.image selectedFine.embedding
            (wz2PaperFullFiberIndices
              selectedFine.family selectedCoarse.family selectedParent) =
          wz2PaperFullFiberIndices
            merged.merged.family ambientCoarse
            (selectedCoarse.embedding selectedParent) := by
    intro selectedParent
    ext ambientSource
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨source, hsourceMem, rfl⟩
      have hparent :
          callerCover.parent source = selectedParent :=
        (callerCover.parent_unique source selectedParent <|
          (mem_wz2PaperFullFiberIndices_iff
            selectedParent source).mp hsourceMem).symm
      apply
        (mem_wz2PaperFullFiberIndices_iff
          (selectedCoarse.embedding selectedParent)
          (selectedFine.embedding source)).mpr
      rw [← hparent, parentAmbient]
      exact
        merged.callerCover.parent_covers
          (selectedFine.embedding source)
    · intro hsource
      have hsourceParent :
          merged.callerCover.parent ambientSource =
            selectedCoarse.embedding selectedParent :=
        (merged.callerCover.parent_unique
          ambientSource (selectedCoarse.embedding selectedParent)
          ((mem_wz2PaperFullFiberIndices_iff
            (selectedCoarse.embedding selectedParent)
            ambientSource).mp hsource)).symm
      have sourceSelected : ambientSource ∈ selectedFineIndices := by
        exact
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ ambientSource,
              ⟨selectedParent, hsourceParent⟩⟩
      rcases selectedAmbientSurjective ambientSource sourceSelected with
        ⟨source, hsourceEq⟩
      have hparent : callerCover.parent source = selectedParent := by
        apply selectedCoarse.embedding.injective
        rw [parentAmbient, hsourceEq, hsourceParent]
      refine
        Finset.mem_image.mpr
          ⟨source,
            (mem_wz2PaperFullFiberIndices_iff
              selectedParent source).mpr <| by
                rw [← hparent]
                exact callerCover.parent_covers source,
            hsourceEq⟩
  have coarseDistinct :
      WZ1PaperIsEssentiallyDistinct selectedCoarse.family :=
    merged.section6Cover.coarse_essentially_distinct.subfamily
      selectedCoarse.toTubeSubfamily
  let section6Cover :
      PureWZ2Section6Cover
        selectedFine.family selectedCoarse.family :=
    {
      fine_line_class :=
        merged.section6Cover.fine_line_class.subfamily selectedFine
      coarse_line_class :=
        merged.section6Cover.coarse_line_class.subfamily
          selectedCoarse.toTubeSubfamily
      covers := fun source =>
        ⟨callerCover.parent source,
          callerCover.parent_covers source⟩
      parent_hit := by
        intro coarseParent
        rcases callerCover.parent_surjective coarseParent with
          ⟨source, hsource⟩
        refine ⟨source, ?_⟩
        rw [← hsource]
        exact callerCover.parent_covers source
      coarse_essentially_distinct := coarseDistinct
    }
  have fiberCWA :
      ∀ selectedParent : Fin selectedCoarse.family.card,
        WZ2PaperPureCWAAtNearbyScales
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            selectedFine.family
            (wz2PaperFullFiberIndices
              selectedFine.family selectedCoarse.family
              selectedParent)).family
          outputConstant := by
    intro selectedParent
    let localSet :=
      wz2PaperFullFiberIndices
        selectedFine.family selectedCoarse.family selectedParent
    let ambientSet :=
      wz2PaperFullFiberIndices
        merged.merged.family ambientCoarse
        (selectedCoarse.embedding selectedParent)
    let localFiber :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        selectedFine.family localSet
    let ambientFiber :=
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        merged.merged.family ambientSet
    let localAmbient :
        Fin localFiber.family.card → Fin merged.merged.family.card :=
      fun index => selectedFine.embedding (localFiber.embedding index)
    have localAmbientMem :
        ∀ index,
          localAmbient index ∈
            wz2PaperFullFiberIndices
              merged.merged.family ambientCoarse
              (selectedCoarse.embedding selectedParent) := by
      intro index
      have hlocal :
          localFiber.embedding index ∈ localSet := by
        change localSet.orderEmbOfFin rfl index ∈ localSet
        exact Finset.orderEmbOfFin_mem localSet rfl index
      have himage :
          localAmbient index ∈
            Finset.image selectedFine.embedding
              (wz2PaperFullFiberIndices
                selectedFine.family selectedCoarse.family
                selectedParent) :=
        Finset.mem_image.mpr
          ⟨localFiber.embedding index, hlocal, rfl⟩
      rwa [fullFiberComplete selectedParent] at himage
    let indexMap :
        Fin localFiber.family.card → Fin ambientFiber.family.card :=
      fun index =>
        ambientSet.orderIsoOfFin rfl |>.symm
          ⟨localAmbient index, localAmbientMem index⟩
    have indexMapInjective : Function.Injective indexMap := by
      intro first second hmap
      apply localFiber.embedding.injective
      apply selectedFine.embedding.injective
      have hsub :
          (⟨localAmbient first, localAmbientMem first⟩ : ambientSet) =
            ⟨localAmbient second, localAmbientMem second⟩ := by
        apply (ambientSet.orderIsoOfFin rfl).symm.injective
        exact hmap
      have hambient := congrArg Subtype.val hsub
      exact hambient
    have indexMapSurjective : Function.Surjective indexMap := by
      intro ambientIndex
      let ambientSource := ambientFiber.embedding ambientIndex
      have ambientMem :
          ambientSource ∈ ambientSet := by
        change ambientSet.orderEmbOfFin rfl ambientIndex ∈ ambientSet
        exact Finset.orderEmbOfFin_mem ambientSet rfl ambientIndex
      have imageMem :
          ambientSource ∈
            Finset.image selectedFine.embedding
              (wz2PaperFullFiberIndices
                selectedFine.family selectedCoarse.family
                selectedParent) := by
        rw [fullFiberComplete selectedParent]
        exact ambientMem
      rcases Finset.mem_image.mp imageMem with
        ⟨selectedSource, selectedMem, hselected⟩
      let localIndex : Fin localFiber.family.card :=
        localSet.orderIsoOfFin rfl |>.symm
          ⟨selectedSource, selectedMem⟩
      have hlocalEmbedding :
          localFiber.embedding localIndex = selectedSource := by
        change
          localSet.orderEmbOfFin rfl localIndex = selectedSource
        exact
          congrArg Subtype.val <|
            localSet.orderIsoOfFin rfl |>.apply_symm_apply
              ⟨selectedSource, selectedMem⟩
      refine ⟨localIndex, ?_⟩
      apply ambientFiber.embedding.injective
      have hindexMapAmbient :
          ambientFiber.embedding (indexMap localIndex) =
            localAmbient localIndex := by
        change
          ambientSet.orderEmbOfFin rfl
              (ambientSet.orderIsoOfFin rfl |>.symm
                ⟨localAmbient localIndex,
                  localAmbientMem localIndex⟩) =
            localAmbient localIndex
        exact
          congrArg Subtype.val <|
            ambientSet.orderIsoOfFin rfl |>.apply_symm_apply
              ⟨localAmbient localIndex,
                localAmbientMem localIndex⟩
      rw [hindexMapAmbient]
      change localAmbient localIndex = ambientSource
      dsimp only [localAmbient]
      rw [hlocalEmbedding, hselected]
    let indexEquiv :
        Fin localFiber.family.card ≃ Fin ambientFiber.family.card :=
      Equiv.ofBijective indexMap
        ⟨indexMapInjective, indexMapSurjective⟩
    have tubeEq :
        ∀ index,
          localFiber.family.tube index =
            ambientFiber.family.tube (indexEquiv index) := by
      intro index
      rw [localFiber.tube_eq, ambientFiber.tube_eq,
        selectedFine.tube_eq]
      have hambient :
          ambientFiber.embedding (indexEquiv index) =
            localAmbient index := by
        change
          ambientSet.orderEmbOfFin rfl (indexMap index) =
            localAmbient index
        exact
          congrArg Subtype.val <|
            ambientSet.orderIsoOfFin rfl |>.apply_symm_apply
              ⟨localAmbient index, localAmbientMem index⟩
      rw [hambient]
    exact
      (merged.fiber_pure_cwa
        (selectedCoarse.embedding selectedParent)).reindex
          indexEquiv tubeEq
  exact
    ⟨{
      selectedFineIndices := selectedFineIndices
      selectedFineIndices_eq := rfl
      selectedFine := selectedFine
      selectedFine_eq := rfl
      selectedFineShading := selectedFineShading
      selectedFineShading_eq := rfl
      callerCover := callerCover
      section6Cover := section6Cover
      parent_ambient_eq := parentAmbient
      full_fiber_complete := fullFiberComplete
      fiber_pure_cwa := fiberCWA
    }⟩

namespace PureWZ2SelectedCallerCompletePullbackData

/-- Complete caller pullback preserves each selected caller's shaded mass. -/
theorem full_fiber_mass_eq
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
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {selectedCoarse :
      WZ2PaperPureTubeSubfamily
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family}
    (data :
      PureWZ2SelectedCallerCompletePullbackData
        merged selectedCoarse)
    (parent : Fin selectedCoarse.family.card) :
    (∑ source ∈
        wz2PaperFullFiberIndices
          data.selectedFine.family selectedCoarse.family parent,
      volume (data.selectedFineShading.carrier source)) =
      ∑ source ∈
        wz2PaperFullFiberIndices
          merged.merged.family
          (quotient.callerCover.hitParentSubfamily
            quotient.positiveCallerFine).family
          (selectedCoarse.embedding parent),
        volume (merged.mergedShading.carrier source) := by
  rw [data.selectedFineShading_eq]
  change
    (∑ source ∈
        wz2PaperFullFiberIndices
          data.selectedFine.family selectedCoarse.family parent,
      volume
        (merged.mergedShading.carrier
          (data.selectedFine.embedding source))) =
      _
  let localSet :=
    wz2PaperFullFiberIndices
      data.selectedFine.family selectedCoarse.family parent
  let ambientSet :=
    wz2PaperFullFiberIndices
      merged.merged.family
      (quotient.callerCover.hitParentSubfamily
        quotient.positiveCallerFine).family
      (selectedCoarse.embedding parent)
  let mass : Fin merged.merged.family.card → ENNReal :=
    fun source => volume (merged.mergedShading.carrier source)
  have hsumImage :
      (∑ source ∈ localSet,
          mass (data.selectedFine.embedding source)) =
        ∑ ambientSource ∈
            Finset.image data.selectedFine.embedding localSet,
          mass ambientSource := by
    exact
      (Finset.sum_image
        (s := localSet)
        (f := mass)
        data.selectedFine.embedding.injective.injOn).symm
  have hcomplete :
      Finset.image data.selectedFine.embedding localSet =
        ambientSet := by
    exact data.full_fiber_complete parent
  calc
    (∑ source ∈ localSet,
        mass (data.selectedFine.embedding source)) =
        ∑ ambientSource ∈
            Finset.image data.selectedFine.embedding localSet,
          mass ambientSource :=
      hsumImage
    _ = ∑ ambientSource ∈ ambientSet, mass ambientSource := by
      rw [hcomplete]

/-- The selected fine mass is the sum of the retained ambient caller-fiber
masses. -/
theorem selectedFineShading_mass_eq
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
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := outputConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {selectedCoarse :
      WZ2PaperPureTubeSubfamily
        (quotient.callerCover.hitParentSubfamily
          quotient.positiveCallerFine).family}
    (data :
      PureWZ2SelectedCallerCompletePullbackData
        merged selectedCoarse) :
    data.selectedFineShading.mass =
      ∑ parent : Fin selectedCoarse.family.card,
        ∑ source ∈
          wz2PaperFullFiberIndices
            merged.merged.family
            (quotient.callerCover.hitParentSubfamily
              quotient.positiveCallerFine).family
            (selectedCoarse.embedding parent),
          volume (merged.mergedShading.carrier source) := by
  have fiberIndices :
      ∀ parent : Fin selectedCoarse.family.card,
        wz2PaperFullFiberIndices
            data.selectedFine.family selectedCoarse.family parent =
          data.callerCover.fiberIndices parent := by
    intro parent
    ext source
    simp only [WZ1PaperTubeCover.fiberIndices,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_wz2PaperFullFiberIndices_iff]
    constructor
    · intro hcovered
      exact
        (data.callerCover.parent_unique
          source parent hcovered).symm
    · intro hparent
      rw [← hparent]
      exact data.callerCover.parent_covers source
  have partition :
      (∑ parent : Fin selectedCoarse.family.card,
          ∑ source ∈
            wz2PaperFullFiberIndices
              data.selectedFine.family selectedCoarse.family parent,
            volume (data.selectedFineShading.carrier source)) =
        data.selectedFineShading.mass := by
    simp_rw [fiberIndices]
    change
      (∑ parent : Fin selectedCoarse.family.card,
          ∑ source ∈ Finset.univ with
              data.callerCover.parent source = parent,
            volume (data.selectedFineShading.carrier source)) =
        ∑ source : Fin data.selectedFine.family.card,
          volume (data.selectedFineShading.carrier source)
    exact
      Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ) (t := Finset.univ)
        (g := data.callerCover.parent)
        (fun _ _ => Finset.mem_univ _)
        (fun source =>
          volume (data.selectedFineShading.carrier source))
  rw [← partition]
  apply Finset.sum_congr rfl
  intro parent _
  exact data.full_fiber_mass_eq parent

end PureWZ2SelectedCallerCompletePullbackData

end Kakeya.Assouad

end
