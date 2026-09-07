import MyLeanRepo.Kakeya.Assouad.PropStickySelectedHitCover

/-!
# Realize finite degree regularization as a paper cover

The simultaneous regularization theorem counts selected ambient indices in
the fibers of each parent map.  This module identifies those counts with the
full geometric fibers of the cover restricted to the selected tubes and the
parents they hit.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem
    WZ2PaperPartitioningCover.restrictToHitParents_fullFiberCount_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selectedIndices : Finset (Fin fine.card))
    (parent :
      Fin (cover.hitParentSubfamily
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedIndices)).family.card) :
    wz2PaperFullFiberCount
        (Kakeya.Streamlined.TubeSubfamily.fromFinset
          fine selectedIndices).family
        (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)).family
        parent =
      ((selectedIndices.filter fun source =>
        cover.parent source =
          (cover.hitParentSubfamily
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices)).embedding parent).card :
        ENNReal) := by
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine selectedIndices
  let hitCoarse := cover.hitParentSubfamily selected
  let restricted := cover.restrictToHitParents selected
  let selectedFiber : Finset (Fin selected.family.card) :=
    Finset.univ.filter fun source =>
      restricted.parent source = parent
  let ambientFiber : Finset (Fin fine.card) :=
    selectedIndices.filter fun source =>
      cover.parent source = hitCoarse.embedding parent
  have hcard : selectedFiber.card = ambientFiber.card := by
    apply Finset.card_bij
        (fun source _ => selected.embedding source)
    · intro source hsource
      apply Finset.mem_filter.mpr
      refine
        ⟨Finset.orderEmbOfFin_mem selectedIndices rfl source, ?_⟩
      have hparent :
          restricted.parent source = parent :=
        (Finset.mem_filter.mp hsource).2
      have hambient :=
        congrArg hitCoarse.embedding hparent
      simpa [restricted, selected, hitCoarse,
        WZ2PaperPartitioningCover.restrictToHitParents,
        WZ2PaperPartitioningCover.hitParent_ambient] using
        hambient
    · intro first _ second _ heq
      exact selected.embedding.injective heq
    · intro ambient hambient
      have hambientSelected : ambient ∈ selectedIndices :=
        (Finset.mem_filter.mp hambient).1
      let source : Fin selected.family.card :=
        (selectedIndices.orderIsoOfFin rfl).symm
          ⟨ambient, hambientSelected⟩
      refine ⟨source, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        apply hitCoarse.embedding.injective
        change
          (cover.hitParentSubfamily selected).embedding
              (cover.hitParent selected source) =
            (cover.hitParentSubfamily selected).embedding parent
        rw [cover.hitParent_ambient]
        have hsourceAmbient :
            selected.embedding source = ambient := by
          exact congrArg Subtype.val
            ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
              ⟨ambient, hambientSelected⟩)
        rw [hsourceAmbient]
        exact (Finset.mem_filter.mp hambient).2
      · exact congrArg Subtype.val
          ((selectedIndices.orderIsoOfFin rfl).apply_symm_apply
            ⟨ambient, hambientSelected⟩)
  rw [restricted.fullFiberCount_eq parent]
  change
    ((restricted.fiberIndices parent).card : ENNReal) =
      (ambientFiber.card : ENNReal)
  have hfull :
      restricted.fiberIndices parent = selectedFiber := by
    rfl
  rw [hfull]
  exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) hcard

theorem
    WZ2PaperPartitioningCover.restrictToHitParents_fullFiber_uniform
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selectedIndices : Finset (Fin fine.card))
    (constant : ENNReal)
    (hdegree :
      ∀ first second : Fin coarse.card,
        0 <
            (selectedIndices.filter fun source =>
              cover.parent source = first).card →
          0 <
            (selectedIndices.filter fun source =>
              cover.parent source = second).card →
          (((selectedIndices.filter fun source =>
              cover.parent source = first).card : ℕ) : ENNReal) ≤
            constant *
              (((selectedIndices.filter fun source =>
                cover.parent source = second).card : ℕ) : ENNReal)) :
    ∀ first second :
        Fin (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)).family.card,
      wz2PaperFullFiberCount
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices).family
          (cover.hitParentSubfamily
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices)).family
          first ≤
        constant *
          wz2PaperFullFiberCount
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices).family
            (cover.hitParentSubfamily
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                fine selectedIndices)).family
            second := by
  intro first second
  rw [
    cover.restrictToHitParents_fullFiberCount_eq
      selectedIndices first,
    cover.restrictToHitParents_fullFiberCount_eq
      selectedIndices second]
  apply hdegree
  · apply Finset.card_pos.mpr
    have hfirst :
        (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)).embedding first ∈
          cover.hitParentIndices
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices) :=
      Finset.orderEmbOfFin_mem
        (cover.hitParentIndices
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)) rfl first
    rcases Finset.mem_image.mp hfirst with
      ⟨source, _hsource, hsourceParent⟩
    refine ⟨
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedIndices).embedding source, ?_⟩
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.orderEmbOfFin_mem selectedIndices rfl source,
        hsourceParent⟩
  · apply Finset.card_pos.mpr
    have hsecond :
        (cover.hitParentSubfamily
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)).embedding second ∈
          cover.hitParentIndices
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              fine selectedIndices) :=
      Finset.orderEmbOfFin_mem
        (cover.hitParentIndices
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            fine selectedIndices)) rfl second
    rcases Finset.mem_image.mp hsecond with
      ⟨source, _hsource, hsourceParent⟩
    refine ⟨
      (Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedIndices).embedding source, ?_⟩
    apply Finset.mem_filter.mpr
    exact
      ⟨Finset.orderEmbOfFin_mem selectedIndices rfl source,
        hsourceParent⟩

/--
The cardinality of a filtered image equals the cardinality of the
correspondingly filtered source, when the function is injective.
-/
lemma filter_image_card {α β : Type*} [DecidableEq β]
    (f : α → β) (hf : Function.Injective f)
    (s : Finset α) (p : β → Prop) [DecidablePred p] :
    ((s.image f).filter p).card =
      (s.filter (fun x => p (f x))).card := by
  have h1 :
      (s.image f).filter p =
        (s.filter (fun x => p (f x))).image f := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hp⟩
      exact ⟨a, ⟨ha, hp⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hp⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hp⟩
  rw [h1]
  rw [Finset.card_image_of_injective _ hf]

/--
Subfamily-indexed form of strict full-fiber uniformity.
-/
theorem
    WZ2PaperPartitioningCover.restrictToHitParents_fullFiber_uniform_of_subfamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (constant : ENNReal)
    (hdegree :
      ∀ first second : Fin coarse.card,
        0 <
            ((Finset.univ :
                Finset (Fin selected.family.card)).filter
              fun source =>
                cover.parent (selected.embedding source) = first).card →
          0 <
            ((Finset.univ :
                Finset (Fin selected.family.card)).filter
              fun source =>
                cover.parent (selected.embedding source) = second).card →
          ((((Finset.univ :
              Finset (Fin selected.family.card)).filter
            fun source =>
              cover.parent (selected.embedding source) = first).card :
              ℕ) : ENNReal) ≤
            constant *
              ((((Finset.univ :
                  Finset (Fin selected.family.card)).filter
                fun source =>
                  cover.parent (selected.embedding source) = second).card :
                  ℕ) : ENNReal)) :
    ∀ first second :
        Fin (cover.hitParentSubfamily selected).family.card,
      wz2PaperFullFiberCount
          selected.family
          (cover.hitParentSubfamily selected).family first ≤
        constant *
          wz2PaperFullFiberCount
            selected.family
            (cover.hitParentSubfamily selected).family second := by
  intro first second
  let restricted := cover.restrictToHitParents selected
  have hcount :
      ∀ parent :
          Fin (cover.hitParentSubfamily selected).family.card,
        wz2PaperFullFiberCount
            selected.family
            (cover.hitParentSubfamily selected).family parent =
          (((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
            cover.parent (selected.embedding source) =
              (cover.hitParentSubfamily selected).embedding parent).card :
            ENNReal) := by
    intro parent
    rw [restricted.fullFiberCount_eq]
    change
      (((Finset.univ :
          Finset (Fin selected.family.card)).filter fun source =>
        restricted.parent source = parent).card : ENNReal) =
      (((Finset.univ :
          Finset (Fin selected.family.card)).filter fun source =>
        cover.parent (selected.embedding source) =
          (cover.hitParentSubfamily selected).embedding parent).card :
        ENNReal)
    have hfinset :
        ((Finset.univ :
            Finset (Fin selected.family.card)).filter fun source =>
          restricted.parent source = parent) =
        ((Finset.univ :
            Finset (Fin selected.family.card)).filter fun source =>
          cover.parent (selected.embedding source) =
            (cover.hitParentSubfamily selected).embedding parent) := by
      ext source
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hparent
        have hambient :=
          congrArg
            (cover.hitParentSubfamily selected).embedding hparent
        simpa [restricted,
          WZ2PaperPartitioningCover.restrictToHitParents] using
          hambient
      · intro hambient
        apply
          (cover.hitParentSubfamily selected).embedding.injective
        simpa [restricted,
          WZ2PaperPartitioningCover.restrictToHitParents] using
          hambient
    rw [hfinset]
  rw [hcount first, hcount second]
  apply hdegree
  · apply Finset.card_pos.mpr
    rcases cover.hitParent_surjective selected first with
      ⟨source, hsource⟩
    refine ⟨source, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩⟩
    have hambient := congrArg
      (cover.hitParentSubfamily selected).embedding hsource
    rw [cover.hitParent_ambient] at hambient
    exact hambient
  · apply Finset.card_pos.mpr
    rcases cover.hitParent_surjective selected second with
      ⟨source, hsource⟩
    refine ⟨source, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ?_⟩⟩
    have hambient := congrArg
      (cover.hitParentSubfamily selected).embedding hsource
    rw [cover.hitParent_ambient] at hambient
    exact hambient

/--
Convert regularization degree uniformity over a subfamily into the
corresponding degree uniformity over its ambient image.
-/
theorem WZ2PaperPartitioningCover.regularizationDegree_to_ambientDegree
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (ambientSelected : Kakeya.Streamlined.TubeSubfamily fine)
    (regularizedSelected :
      Finset (Fin ambientSelected.family.card))
    (constant : ENNReal)
    (selectedIndices : Finset (Fin fine.card))
    (hsel :
      selectedIndices =
        regularizedSelected.image ambientSelected.embedding)
    (hdegree_reg :
      ∀ (first second : Fin coarse.card),
        0 <
            (regularizedSelected.filter
              (fun index =>
                cover.parent
                    (ambientSelected.embedding index) =
                  first)).card →
        0 <
            (regularizedSelected.filter
              (fun index =>
                cover.parent
                    (ambientSelected.embedding index) =
                  second)).card →
        ((regularizedSelected.filter
              (fun index =>
                cover.parent
                    (ambientSelected.embedding index) =
                  first)).card : ENNReal) ≤
          constant *
            ((regularizedSelected.filter
              (fun index =>
                cover.parent
                    (ambientSelected.embedding index) =
                  second)).card : ENNReal)) :
    ∀ (first second : Fin coarse.card),
      0 <
          (selectedIndices.filter
            (fun source => cover.parent source = first)).card →
      0 <
          (selectedIndices.filter
            (fun source => cover.parent source = second)).card →
      ((selectedIndices.filter
            (fun source => cover.parent source = first)).card :
          ENNReal) ≤
        constant *
          ((selectedIndices.filter
            (fun source => cover.parent source = second)).card :
            ENNReal) := by
  have h_card : ∀ (p : Fin coarse.card),
      (selectedIndices.filter
          (fun source => cover.parent source = p)).card =
        (regularizedSelected.filter
          (fun index =>
            cover.parent (ambientSelected.embedding index) =
              p)).card := by
    intro p
    rw [hsel]
    exact
      filter_image_card
        ambientSelected.embedding
        ambientSelected.embedding.injective
        regularizedSelected
        (fun source => cover.parent source = p)
  intro first second h1 h2
  have h1' :
      0 <
        (regularizedSelected.filter
          (fun index =>
            cover.parent (ambientSelected.embedding index) =
              first)).card := by
    rw [← h_card first]
    exact h1
  have h2' :
      0 <
        (regularizedSelected.filter
          (fun index =>
            cover.parent (ambientSelected.embedding index) =
              second)).card := by
    rw [← h_card second]
    exact h2
  have h_main := hdegree_reg first second h1' h2'
  rw [h_card first, h_card second]
  exact h_main

end Kakeya.Assouad

end
