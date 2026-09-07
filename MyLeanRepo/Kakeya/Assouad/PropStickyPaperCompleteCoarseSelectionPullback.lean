import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteCoarseSelectionPullbackStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex

/-! # Complete-fiber pullback of a coarse tube selection -/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_complete_coarse_selection_pullback :
    WZ2PaperCompleteCoarseSelectionPullbackStatement := by
  intro delta rho fine coarse cover fineShading coarseShading
    hFineCubical hCoarseCubical hCompatibility selectedCoarse
  let selectedFineIndices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      ∃ parent : Fin selectedCoarse.family.card,
        cover.parent source = selectedCoarse.embedding parent
  let selectedFine : Kakeya.Streamlined.TubeSubfamily fine :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine selectedFineIndices
  let selectedFineShading : WZ1PaperTubeShading selectedFine.family :=
    restrictPaperShading selectedFine fineShading
  have hSelectedMem :
      ∀ index : Fin selectedFine.family.card,
        selectedFine.embedding index ∈ selectedFineIndices :=
    fun index =>
      Finset.orderEmbOfFin_mem selectedFineIndices rfl index
  have hParentExists :
      ∀ index : Fin selectedFine.family.card,
        ∃ parent : Fin selectedCoarse.family.card,
          cover.parent (selectedFine.embedding index) =
            selectedCoarse.embedding parent := by
    intro index
    exact (Finset.mem_filter.mp (hSelectedMem index)).2
  let parent :
      Fin selectedFine.family.card →
        Fin selectedCoarse.family.card :=
    fun index => Classical.choose (hParentExists index)
  have hParentAmbient :
      ∀ index,
        selectedCoarse.embedding (parent index) =
          cover.parent (selectedFine.embedding index) := by
    intro index
    exact (Classical.choose_spec (hParentExists index)).symm
  have hSelectedSurjective :
      ∀ sourceIndex ∈ selectedFineIndices,
        ∃ index : Fin selectedFine.family.card,
          selectedFine.embedding index = sourceIndex := by
    intro sourceIndex hsource
    let member : selectedFineIndices := ⟨sourceIndex, hsource⟩
    let index : Fin selectedFine.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm member
    exact
      ⟨index,
        congrArg Subtype.val
          (selectedFineIndices.orderIsoOfFin rfl
            |>.apply_symm_apply member)⟩
  have hParentSurjective : Function.Surjective parent := by
    intro selectedParent
    let ambientParent := selectedCoarse.embedding selectedParent
    rcases cover.parent_surjective ambientParent with
      ⟨ambientSource, hsourceParent⟩
    have hsourceSelected : ambientSource ∈ selectedFineIndices := by
      apply Finset.mem_filter.mpr
      exact
        ⟨Finset.mem_univ _,
          ⟨selectedParent, hsourceParent⟩⟩
    rcases hSelectedSurjective ambientSource hsourceSelected with
      ⟨index, hindex⟩
    refine ⟨index, ?_⟩
    apply selectedCoarse.embedding.injective
    rw [hParentAmbient index, hindex, hsourceParent]
  let restrictedCover :
      WZ2PaperPartitioningCover
        selectedFine.family selectedCoarse.family :=
    {
      parent := parent
      parent_surjective := hParentSurjective
      parent_covers := by
        intro index
        rw [selectedFine.tube_eq, selectedCoarse.tube_eq,
          hParentAmbient]
        exact cover.parent_covers (selectedFine.embedding index)
      parent_unique := by
        intro index candidate hcovered
        apply selectedCoarse.embedding.injective
        rw [hParentAmbient]
        apply cover.parent_unique (selectedFine.embedding index)
        rw [← selectedFine.tube_eq index,
          ← selectedCoarse.tube_eq candidate]
        exact hcovered
      parent_carrier_covers := by
        intro index
        rw [selectedFine.tube_eq, selectedCoarse.tube_eq,
          hParentAmbient]
        exact cover.parent_carrier_covers
          (selectedFine.embedding index)
      literal_parent_unique := by
        intro index candidate hcovered
        apply selectedCoarse.embedding.injective
        rw [hParentAmbient]
        apply cover.literal_parent_unique
          (selectedFine.embedding index)
          (selectedCoarse.embedding candidate)
        rw [← selectedFine.tube_eq index,
          ← selectedCoarse.tube_eq candidate]
        exact hcovered
      literal_doubled_fibers_disjoint := by
        intro first second hne
        have hambientNe :
            selectedCoarse.embedding first ≠
              selectedCoarse.embedding second :=
          selectedCoarse.embedding.injective.ne hne
        rw [Finset.disjoint_left]
        intro index hfirst hsecond
        have hfirstAmbient :
            selectedFine.embedding index ∈
              wz2PaperLiteralDoubledFiberIndices
                fine coarse (selectedCoarse.embedding first) := by
          simpa [wz2PaperLiteralDoubledFiberIndices,
            selectedFine.tube_eq index,
            selectedCoarse.tube_eq first] using hfirst
        have hsecondAmbient :
            selectedFine.embedding index ∈
              wz2PaperLiteralDoubledFiberIndices
                fine coarse (selectedCoarse.embedding second) := by
          simpa [wz2PaperLiteralDoubledFiberIndices,
            selectedFine.tube_eq index,
            selectedCoarse.tube_eq second] using hsecond
        exact
          ((Finset.disjoint_left.mp
            (cover.literal_doubled_fibers_disjoint
              (selectedCoarse.embedding first)
              (selectedCoarse.embedding second)
              hambientNe))
            hfirstAmbient) hsecondAmbient
      doubled_fibers_disjoint := by
        intro first second hne
        have hambientNe :
            selectedCoarse.embedding first ≠
              selectedCoarse.embedding second :=
          selectedCoarse.embedding.injective.ne hne
        rw [Finset.disjoint_left]
        intro index hfirst hsecond
        have hfirstAmbient :
            selectedFine.embedding index ∈
              wz2PaperDoubledFiberIndices
                fine coarse (selectedCoarse.embedding first) := by
          simpa [wz2PaperDoubledFiberIndices,
            selectedFine.tube_eq index,
            selectedCoarse.tube_eq first] using hfirst
        have hsecondAmbient :
            selectedFine.embedding index ∈
              wz2PaperDoubledFiberIndices
                fine coarse (selectedCoarse.embedding second) := by
          simpa [wz2PaperDoubledFiberIndices,
            selectedFine.tube_eq index,
            selectedCoarse.tube_eq second] using hsecond
        exact
          ((Finset.disjoint_left.mp
            (cover.doubled_fibers_disjoint
              (selectedCoarse.embedding first)
              (selectedCoarse.embedding second)
              hambientNe))
            hfirstAmbient) hsecondAmbient
    }
  have hFullFiberComplete :
      ∀ selectedParent : Fin selectedCoarse.family.card,
        Finset.image selectedFine.embedding
            (wz2PaperFullFiberIndices
              selectedFine.family selectedCoarse.family selectedParent) =
          wz2PaperFullFiberIndices
            fine coarse (selectedCoarse.embedding selectedParent) := by
    intro selectedParent
    ext ambientSource
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨index, hindex, rfl⟩
      have hparent :
          restrictedCover.parent index = selectedParent :=
        (restrictedCover.mem_fullFiber_iff_parent
          selectedParent index).mp hindex
      change parent index = selectedParent at hparent
      exact
        (cover.mem_fullFiber_iff_parent
          (selectedCoarse.embedding selectedParent)
          (selectedFine.embedding index)).mpr
          (by rw [← hParentAmbient index, hparent])
    · intro hsource
      have hsourceParent :
          cover.parent ambientSource =
            selectedCoarse.embedding selectedParent :=
        (cover.mem_fullFiber_iff_parent
          (selectedCoarse.embedding selectedParent)
          ambientSource).mp hsource
      have hsourceSelected :
          ambientSource ∈ selectedFineIndices := by
        apply Finset.mem_filter.mpr
        exact
          ⟨Finset.mem_univ _,
            ⟨selectedParent, hsourceParent⟩⟩
      rcases hSelectedSurjective ambientSource hsourceSelected with
        ⟨index, hindex⟩
      have hparent : restrictedCover.parent index = selectedParent := by
        apply selectedCoarse.embedding.injective
        rw [hParentAmbient index, hindex, hsourceParent]
      exact
        ⟨index,
          (restrictedCover.mem_fullFiber_iff_parent
            selectedParent index).mpr hparent,
          hindex⟩
  let selectedCoarseShading :
      WZ1PaperTubeShading selectedCoarse.family :=
    restrictPaperShading selectedCoarse coarseShading
  have hPointCompatibility :
      ∀ source point,
        point ∈ selectedFineShading.carrier source →
          point ∈
            selectedCoarseShading.carrier
              (restrictedCover.parent source) := by
    intro source point hpoint
    have hAmbient :
        point ∈
          coarseShading.carrier
            (cover.parent (selectedFine.embedding source)) :=
      hCompatibility (selectedFine.embedding source) point hpoint
    change
      point ∈
        coarseShading.carrier
          (selectedCoarse.embedding
            (restrictedCover.parent source))
    rw [hParentAmbient source]
    exact hAmbient
  exact
    ⟨{
      selectedFineIndices := selectedFineIndices
      selectedFineIndices_eq := rfl
      selectedFine := selectedFine
      selectedFine_eq := rfl
      selectedFineShading := selectedFineShading
      selectedFineShading_eq := rfl
      selectedFine_subshading := fun _ => Set.Subset.rfl
      selectedFine_cubical :=
        restrictPaperShading_cubical selectedFine hFineCubical
      parent := parent
      parent_ambient_eq := hParentAmbient
      restrictedCover := restrictedCover
      restricted_parent_eq := fun _ => rfl
      full_fiber_complete := hFullFiberComplete
      selectedCoarseShading := selectedCoarseShading
      selectedCoarseShading_eq := rfl
      selectedCoarse_cubical :=
        restrictPaperShading_cubical selectedCoarse hCoarseCubical
      point_compatibility := hPointCompatibility
    }⟩

/--
Restricting to complete selected parent fibers preserves each retained fiber's
shaded mass exactly.
-/
theorem WZ2PaperCompleteCoarseSelectionPullbackData.full_fiber_mass_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse}
    (data :
      WZ2PaperCompleteCoarseSelectionPullbackData
        cover fineShading coarseShading selectedCoarse)
    (parent : Fin selectedCoarse.family.card) :
    (restrictPaperShading
        (data.restrictedCover.fullFiberSubfamily parent)
        data.selectedFineShading).mass =
      (restrictPaperShading
        (cover.fullFiberSubfamily (selectedCoarse.embedding parent))
        fineShading).mass := by
  rcases
      wz2_paper_complete_fiber_reindex
        cover data.selectedFine data.restrictedCover
        parent (selectedCoarse.embedding parent)
        (data.full_fiber_complete parent)
    with ⟨reindex⟩
  let localFiber :=
    data.restrictedCover.fullFiberSubfamily parent
  let ambientFiber :=
    cover.fullFiberSubfamily (selectedCoarse.embedding parent)
  let equivalence :
      Fin localFiber.family.card ≃ Fin ambientFiber.family.card :=
    Equiv.ofBijective reindex.localIndex reindex.localIndex_bijective
  change
    (∑ index : Fin localFiber.family.card,
        MeasureTheory.volume
          (data.selectedFineShading.carrier
            (localFiber.embedding index))) =
      ∑ index : Fin ambientFiber.family.card,
        MeasureTheory.volume
          (fineShading.carrier (ambientFiber.embedding index))
  exact
    Fintype.sum_equiv equivalence
      (fun index : Fin localFiber.family.card =>
        MeasureTheory.volume
          (data.selectedFineShading.carrier
            (localFiber.embedding index)))
      (fun index : Fin ambientFiber.family.card =>
        MeasureTheory.volume
          (fineShading.carrier (ambientFiber.embedding index)))
      (fun index => by
        have hAmbient := reindex.ambient_eq index
        rw [data.selectedFineShading_eq]
        change
          MeasureTheory.volume
              (fineShading.carrier
                (data.selectedFine.embedding
                  (localFiber.embedding index))) =
            MeasureTheory.volume
              (fineShading.carrier
                (ambientFiber.embedding (reindex.localIndex index)))
        rw [hAmbient])

/--
Restricting to complete selected parent fibers also preserves the point
multiplicity of each retained fiber.  This is the finite-index form of the
paper's instruction to refine later shadings while preserving the already
chosen common `mu_fine`.
-/
theorem WZ2PaperCompleteCoarseSelectionPullbackData.full_fiber_pointMultiplicity_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse}
    (data :
      WZ2PaperCompleteCoarseSelectionPullbackData
        cover fineShading coarseShading selectedCoarse)
    (parent : Fin selectedCoarse.family.card)
    (point : Point3) :
    (restrictPaperShading
        (data.restrictedCover.fullFiberSubfamily parent)
        data.selectedFineShading).pointMultiplicity point =
      (restrictPaperShading
        (cover.fullFiberSubfamily (selectedCoarse.embedding parent))
        fineShading).pointMultiplicity point := by
  rcases
      wz2_paper_complete_fiber_reindex
        cover data.selectedFine data.restrictedCover
        parent (selectedCoarse.embedding parent)
        (data.full_fiber_complete parent)
    with ⟨reindex⟩
  let localFiber :=
    data.restrictedCover.fullFiberSubfamily parent
  let ambientFiber :=
    cover.fullFiberSubfamily (selectedCoarse.embedding parent)
  rw [data.selectedFineShading_eq]
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

/--
The selected fine mass is exactly the sum of the retained ambient complete
fiber masses.
-/
theorem WZ2PaperCompleteCoarseSelectionPullbackData.selectedFineShading_mass_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse}
    (data :
      WZ2PaperCompleteCoarseSelectionPullbackData
        cover fineShading coarseShading selectedCoarse) :
    data.selectedFineShading.mass =
      ∑ parent : Fin selectedCoarse.family.card,
        (restrictPaperShading
          (cover.fullFiberSubfamily
            (selectedCoarse.embedding parent))
          fineShading).mass := by
  rw [← data.restrictedCover.sum_fullFiberShading_mass
    data.selectedFineShading]
  apply Finset.sum_congr rfl
  intro parent _
  exact data.full_fiber_mass_eq parent

end Kakeya.Assouad

end
