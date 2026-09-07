import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Reindex a complete selected full fiber

When a parentwise selection retains every ambient child of a selected parent,
the final full fiber and the ambient full fiber differ only by finite
indexing.  This module packages the canonical equivalence induced by their
ambient embeddings.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure WZ2PaperCompleteFiberReindexData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    {selectedCoarse : Kakeya.Streamlined.TubeFamily rho}
    (restrictedCover :
      WZ2PaperPartitioningCover selected.family selectedCoarse)
    (parent : Fin selectedCoarse.card)
    (ambientParent : Fin coarse.card)
    (complete :
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family selectedCoarse parent) =
        wz2PaperFullFiberIndices fine coarse ambientParent) where
  localIndex :
    Fin (restrictedCover.fullFiberSubfamily parent).family.card →
      Fin (cover.fullFiberSubfamily ambientParent).family.card
  localIndex_bijective : Function.Bijective localIndex
  ambient_eq :
    ∀ index,
      selected.embedding
          ((restrictedCover.fullFiberSubfamily parent).embedding index) =
        (cover.fullFiberSubfamily ambientParent).embedding
          (localIndex index)

theorem wz2_paper_complete_fiber_reindex
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    {selectedCoarse : Kakeya.Streamlined.TubeFamily rho}
    (restrictedCover :
      WZ2PaperPartitioningCover selected.family selectedCoarse)
    (parent : Fin selectedCoarse.card)
    (ambientParent : Fin coarse.card)
    (complete :
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family selectedCoarse parent) =
        wz2PaperFullFiberIndices fine coarse ambientParent) :
    Nonempty
      (WZ2PaperCompleteFiberReindexData
        cover selected restrictedCover parent ambientParent complete) := by
  let selectedIndices :=
    wz2PaperFullFiberIndices
      selected.family selectedCoarse parent
  let ambientIndices :=
    wz2PaperFullFiberIndices fine coarse ambientParent
  let selectedFiber := restrictedCover.fullFiberSubfamily parent
  let ambientFiber := cover.fullFiberSubfamily ambientParent
  let selectedEnumeration : Fin selectedIndices.card ≃ selectedIndices :=
    (selectedIndices.orderIsoOfFin rfl).toEquiv
  let ambientEnumeration : Fin ambientIndices.card ≃ ambientIndices :=
    (ambientIndices.orderIsoOfFin rfl).toEquiv
  have selectedFiber_card :
      selectedFiber.family.card = selectedIndices.card := by
    rfl
  have ambientFiber_card :
      ambientFiber.family.card = ambientIndices.card := by
    rfl
  let ambientOf :
      Fin selectedFiber.family.card → Fin fine.card :=
    fun index =>
      selected.embedding (selectedFiber.embedding index)
  have ambientOf_mem :
      ∀ index, ambientOf index ∈ ambientIndices := by
    intro index
    have selected_mem :
        selectedFiber.embedding index ∈ selectedIndices :=
      restrictedCover.fullFiberSubfamily_mem parent index
    have image_mem :
        ambientOf index ∈
          Finset.image selected.embedding selectedIndices :=
      Finset.mem_image.mpr
        ⟨selectedFiber.embedding index, selected_mem, rfl⟩
    rwa [complete] at image_mem
  let localIndex :
      Fin selectedFiber.family.card →
        Fin ambientFiber.family.card :=
    fun index =>
      cast (congrArg Fin ambientFiber_card.symm) <|
        ambientEnumeration.symm
          ⟨ambientOf index, ambientOf_mem index⟩
  have ambient_eq :
      ∀ index,
        ambientOf index =
          ambientFiber.embedding (localIndex index) := by
    intro index
    change
      ambientOf index =
        (ambientIndices.orderEmbOfFin rfl)
          (cast (congrArg Fin ambientFiber_card) (localIndex index))
    dsimp only [localIndex]
    simp only [cast_cast, ambientEnumeration]
    exact congrArg Subtype.val
      (ambientEnumeration.apply_symm_apply
        ⟨ambientOf index, ambientOf_mem index⟩).symm
  have localIndex_injective : Function.Injective localIndex := by
    intro first second eq
    apply selectedFiber.embedding.injective
    apply selected.embedding.injective
    change ambientOf first = ambientOf second
    rw [ambient_eq first, ambient_eq second, eq]
  have localIndex_surjective : Function.Surjective localIndex := by
    intro ambientIndex
    let ambientSource :=
      ambientFiber.embedding ambientIndex
    have ambientSource_mem :
        ambientSource ∈ ambientIndices :=
      cover.fullFiberSubfamily_mem ambientParent ambientIndex
    have image_mem :
        ambientSource ∈
          Finset.image selected.embedding selectedIndices := by
      rw [complete]
      exact ambientSource_mem
    rcases Finset.mem_image.mp image_mem with
      ⟨selectedSource, selectedSource_mem, selected_ambient_eq⟩
    let selectedIndex0 : Fin selectedIndices.card :=
      selectedEnumeration.symm
        ⟨selectedSource, selectedSource_mem⟩
    let selectedIndex : Fin selectedFiber.family.card :=
      cast (congrArg Fin selectedFiber_card.symm) selectedIndex0
    have selected_embedding_eq :
        selectedFiber.embedding selectedIndex = selectedSource := by
      change
        (selectedIndices.orderEmbOfFin rfl)
            (cast (congrArg Fin selectedFiber_card) selectedIndex) =
          selectedSource
      dsimp only [selectedIndex]
      simp only [cast_cast, selectedIndex0, selectedEnumeration]
      exact congrArg Subtype.val
        (selectedEnumeration.apply_symm_apply
          ⟨selectedSource, selectedSource_mem⟩)
    refine ⟨selectedIndex, ?_⟩
    apply ambientFiber.embedding.injective
    have finalAmbient :
        ambientOf selectedIndex = ambientSource := by
      change
        selected.embedding (selectedFiber.embedding selectedIndex) =
          ambientSource
      rw [selected_embedding_eq, selected_ambient_eq]
    rw [← ambient_eq selectedIndex, finalAmbient]
  exact
    ⟨{
      localIndex := localIndex
      localIndex_bijective :=
        ⟨localIndex_injective, localIndex_surjective⟩
      ambient_eq := ambient_eq
    }⟩

/--
Restricting an ambient shading to a complete selected parent fiber changes
only the finite indexing of that fiber, not its point multiplicity.
-/
theorem wz2_paper_complete_fiber_restrict_pointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    {selectedCoarse : Kakeya.Streamlined.TubeFamily rho}
    (restrictedCover :
      WZ2PaperPartitioningCover selected.family selectedCoarse)
    (parent : Fin selectedCoarse.card)
    (ambientParent : Fin coarse.card)
    (complete :
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family selectedCoarse parent) =
        wz2PaperFullFiberIndices fine coarse ambientParent)
    (shading : WZ1PaperTubeShading fine)
    (point : Point3) :
    (restrictPaperShading
        (restrictedCover.fullFiberSubfamily parent)
        (restrictPaperShading selected shading)).pointMultiplicity point =
      (restrictPaperShading
        (cover.fullFiberSubfamily ambientParent)
        shading).pointMultiplicity point := by
  rcases
      wz2_paper_complete_fiber_reindex
        cover selected restrictedCover parent ambientParent complete
    with ⟨reindex⟩
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity,
    restrictPaperShading]
  apply Finset.card_bij
    (fun index _ => reindex.localIndex index)
  · intro index hindex
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hpoint := (Finset.mem_filter.mp hindex).2
    rw [← reindex.ambient_eq index]
    exact hpoint
  · intro first _ second _ h
    exact reindex.localIndex_bijective.1 h
  · intro ambientIndex hindex
    rcases reindex.localIndex_bijective.2 ambientIndex with
      ⟨localIndex, hlocal⟩
    refine ⟨localIndex, ?_, hlocal⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hpoint := (Finset.mem_filter.mp hindex).2
    rw [reindex.ambient_eq localIndex, hlocal]
    exact hpoint

end Kakeya.Assouad

end
