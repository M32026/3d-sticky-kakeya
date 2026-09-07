import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.UniformSelectedClassWeight

/-!
# Pure restrictions by complete actual parent fibers

Select actual Definition 2.12 parents and retain every fine tube in each
selected complete strict fiber.  This is the public ordinary-carrier analogue
of the historical complete-parent restriction.

The main inheritance lemma treats a second, finer pure cover.  If equality of
the finer parent implies equality of the selected actual parent, then every
hit finer fiber is either retained in full or discarded in full.  Hence the
restricted finer fibers are exact reindexings of ambient finer fibers and
inherit ambient cardinality uniformity with no loss.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- A pure fine subfamily obtained by retaining complete selected actual
parent fibers. -/
structure PureWZ2CompleteParentRestrictionData
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    (actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse)
    (selectedActualParents :
      Finset (Fin actualCoarse.card)) where
  selectedActualParents_nonempty :
    selectedActualParents.Nonempty

namespace PureWZ2CompleteParentRestrictionData

/-- Ambient fine indices in the selected complete actual fibers. -/
def selectedFineIndices
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (_data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents) :
    Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    actualCover.parent source ∈ selectedActualParents

/-- Canonical pure fine subfamily in the selected complete actual fibers. -/
noncomputable def selectedFine
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents) :
    WZ2PaperPureTubeSubfamily fine :=
  WZ2PaperPureTubeSubfamily.fromFinset
    fine data.selectedFineIndices

/-- Construct the pure complete-parent restriction. -/
noncomputable def pureWZ2CompleteParentRestriction
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    (actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse)
    (selectedActualParents :
      Finset (Fin actualCoarse.card))
    (selectedActualParentsNonempty :
      selectedActualParents.Nonempty) :
    PureWZ2CompleteParentRestrictionData
      actualCover selectedActualParents :=
  {
    selectedActualParents_nonempty :=
      selectedActualParentsNonempty
  }

theorem selectedFine_embedding_mem
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (source : Fin data.selectedFine.family.card) :
    data.selectedFine.embedding source ∈
      data.selectedFineIndices := by
  exact
    Finset.orderEmbOfFin_mem
      data.selectedFineIndices rfl source

theorem selectedFine_parent_mem
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (source : Fin data.selectedFine.family.card) :
    actualCover.parent (data.selectedFine.embedding source) ∈
      selectedActualParents := by
  have hsource := data.selectedFine_embedding_mem source
  unfold selectedFineIndices at hsource
  exact (Finset.mem_filter.mp hsource).2

theorem selectedFine_ambient_surjective
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents) :
    ∀ source ∈ data.selectedFineIndices,
      ∃ selectedSource : Fin data.selectedFine.family.card,
        data.selectedFine.embedding selectedSource = source := by
  intro source hsource
  let member : data.selectedFineIndices :=
    ⟨source, hsource⟩
  let selectedSource : Fin data.selectedFine.family.card :=
    (data.selectedFineIndices.orderIsoOfFin rfl).symm member
  refine ⟨selectedSource, ?_⟩
  change
    data.selectedFineIndices.orderEmbOfFin rfl
        selectedSource =
      source
  exact
    congrArg Subtype.val
      (data.selectedFineIndices.orderIsoOfFin rfl
        |>.apply_symm_apply member)

/-- The selected fine cardinality is the sum of the complete selected actual
fiber cardinalities. -/
theorem selectedFine_enncard_eq_sum_actual_fullFiberCount
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (actualScale_nonneg : 0 ≤ actual) :
    data.selectedFine.family.enncard =
      ∑ parent ∈ selectedActualParents,
        wz2PaperOrdinaryFullFiberCount
          fine actualCoarse parent := by
  have hsum :=
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin fine.card))
      selectedActualParents actualCover.parent
  have hselected :
      (Finset.univ.filter fun source =>
        actualCover.parent source ∈ selectedActualParents) =
        data.selectedFineIndices := by
    rfl
  have hfiber :
      ∀ parent,
        wz2PaperOrdinaryFullFiberCount
            fine actualCoarse parent =
          ((Finset.univ.filter fun source =>
            actualCover.parent source = parent).card : ENNReal) := by
    intro parent
    rw [wz2PaperOrdinaryFullFiberCount]
    have hindices :
        wz2PaperOrdinaryFullFiberIndices
            fine actualCoarse parent =
          Finset.univ.filter fun source =>
            actualCover.parent source = parent := by
      ext source
      rw [actualCover.mem_fullFiber_iff_parent_eq
        actualScale_nonneg parent source]
      simp
    rw [hindices]
  rw [show
    ∑ parent ∈ selectedActualParents,
        wz2PaperOrdinaryFullFiberCount
          fine actualCoarse parent =
      ∑ parent ∈ selectedActualParents,
        ((Finset.univ.filter fun source =>
          actualCover.parent source = parent).card : ENNReal) by
      apply Finset.sum_congr rfl
      intro parent _
      exact hfiber parent]
  rw [← Nat.cast_sum]
  change
    (data.selectedFineIndices.card : ENNReal) =
      ((∑ parent ∈ selectedActualParents,
        (Finset.univ.filter fun source =>
          actualCover.parent source = parent).card : ℕ) : ENNReal)
  exact_mod_cast hsum.symm

/--
If a second cover is finer than the actual cover, every hit second-cover
fiber is retained completely.
-/
theorem finer_hit_fullFiber_complete
    {delta finerScale actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {finerCoarse :
      Kakeya.Streamlined.TubeFamily finerScale}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (finerCover :
      WZ2PaperPurePartitioningCover fine finerCoarse)
    (finerScale_nonneg : 0 ≤ finerScale)
    (nested :
      ∀ first second,
        finerCover.parent first =
            finerCover.parent second →
          actualCover.parent first =
            actualCover.parent second)
    (parent :
      Fin (finerCover.hitParentSubfamily
        data.selectedFine).family.card) :
    Finset.image data.selectedFine.embedding
        (wz2PaperOrdinaryFullFiberIndices
          data.selectedFine.family
          (finerCover.hitParentSubfamily
            data.selectedFine).family parent) =
      wz2PaperOrdinaryFullFiberIndices
        fine finerCoarse
        ((finerCover.hitParentSubfamily
          data.selectedFine).embedding parent) := by
  let restricted :=
    finerCover.restrictToHitParents data.selectedFine
  ext ambientSource
  constructor
  · intro hsource
    rcases Finset.mem_image.mp hsource with
      ⟨selectedSource, selectedMem, rfl⟩
    have hparent :
        finerCover.parent
            (data.selectedFine.embedding selectedSource) =
          (finerCover.hitParentSubfamily
            data.selectedFine).embedding parent := by
      simpa only [
        finerCover.restrictToHitParents_fullFiberIndices_eq
          finerScale_nonneg data.selectedFine parent,
        Finset.mem_filter, Finset.mem_univ, true_and
      ] using selectedMem
    exact
      (finerCover.mem_fullFiber_iff_parent_eq
        finerScale_nonneg
        ((finerCover.hitParentSubfamily
          data.selectedFine).embedding parent)
        (data.selectedFine.embedding selectedSource)).mpr
        hparent
  · intro ambientMem
    rcases
        finerCover.hitParent_surjective
          data.selectedFine parent
      with
      ⟨selectedWitness, hwitness⟩
    have witnessAmbientParent :
        finerCover.parent
            (data.selectedFine.embedding selectedWitness) =
          (finerCover.hitParentSubfamily
            data.selectedFine).embedding parent := by
      rw [← finerCover.hitParent_ambient
        data.selectedFine selectedWitness, hwitness]
    have sourceAmbientParent :
        finerCover.parent ambientSource =
          (finerCover.hitParentSubfamily
            data.selectedFine).embedding parent :=
      (finerCover.mem_fullFiber_iff_parent_eq
        finerScale_nonneg
        ((finerCover.hitParentSubfamily
          data.selectedFine).embedding parent)
        ambientSource).mp ambientMem
    have sourceActualParent :
        actualCover.parent ambientSource =
          actualCover.parent
            (data.selectedFine.embedding selectedWitness) := by
      apply nested
      rw [sourceAmbientParent, witnessAmbientParent]
    have actualSelected :
        actualCover.parent ambientSource ∈
          selectedActualParents := by
      rw [sourceActualParent]
      exact data.selectedFine_parent_mem selectedWitness
    have sourceSelected :
        ambientSource ∈ data.selectedFineIndices := by
      unfold selectedFineIndices
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ ambientSource,
            actualSelected⟩
    rcases
        data.selectedFine_ambient_surjective
          ambientSource sourceSelected
      with
      ⟨selectedSource, hselectedSource⟩
    have selectedParent :
        finerCover.parent
            (data.selectedFine.embedding selectedSource) =
          (finerCover.hitParentSubfamily
            data.selectedFine).embedding parent := by
      rw [hselectedSource, sourceAmbientParent]
    refine
      Finset.mem_image.mpr
        ⟨selectedSource, ?_, hselectedSource⟩
    rw [
      finerCover.restrictToHitParents_fullFiberIndices_eq
        finerScale_nonneg data.selectedFine parent
    ]
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ selectedSource,
          selectedParent⟩

/-- Complete finer fibers inherit ambient uniformity without any loss. -/
theorem finer_restricted_fullFiber_uniform
    {delta finerScale actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {finerCoarse :
      Kakeya.Streamlined.TubeFamily finerScale}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (finerCover :
      WZ2PaperPurePartitioningCover fine finerCoarse)
    (finerScale_nonneg : 0 ≤ finerScale)
    (nested :
      ∀ first second,
        finerCover.parent first =
            finerCover.parent second →
          actualCover.parent first =
            actualCover.parent second)
    {C : ENNReal}
    (ambientUniform :
      WZ2PaperPureFullFibersAreCUniform
        fine finerCoarse C) :
    WZ2PaperPureFullFibersAreCUniform
      data.selectedFine.family
      (finerCover.hitParentSubfamily
        data.selectedFine).family C := by
  intro first second
  rw [wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount]
  have firstComplete :=
    data.finer_hit_fullFiber_complete
      finerCover finerScale_nonneg nested first
  have secondComplete :=
    data.finer_hit_fullFiber_complete
      finerCover finerScale_nonneg nested second
  have firstCard :
      (wz2PaperOrdinaryFullFiberIndices
        data.selectedFine.family
        (finerCover.hitParentSubfamily
          data.selectedFine).family first).card =
      (wz2PaperOrdinaryFullFiberIndices
        fine finerCoarse
        ((finerCover.hitParentSubfamily
          data.selectedFine).embedding first)).card := by
    rw [← firstComplete]
    exact
      Finset.card_image_of_injective _
        data.selectedFine.embedding.injective |>.symm
  have secondCard :
      (wz2PaperOrdinaryFullFiberIndices
        data.selectedFine.family
        (finerCover.hitParentSubfamily
          data.selectedFine).family second).card =
      (wz2PaperOrdinaryFullFiberIndices
        fine finerCoarse
        ((finerCover.hitParentSubfamily
          data.selectedFine).embedding second)).card := by
    rw [← secondComplete]
    exact
      Finset.card_image_of_injective _
        data.selectedFine.embedding.injective |>.symm
  rw [firstCard, secondCard]
  exact
    ambientUniform
      ((finerCover.hitParentSubfamily
        data.selectedFine).embedding first)
      ((finerCover.hitParentSubfamily
        data.selectedFine).embedding second)

/--
For a cover coarser than the actual cover, one restricted coarse fiber is the
disjoint union of the selected actual fibers mapped to that coarse parent.
-/
theorem coarser_restricted_fullFiberCount_eq_selected_actual_sum
    {delta actual coarserScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {coarserCoarse :
      Kakeya.Streamlined.TubeFamily coarserScale}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (coarserCover :
      WZ2PaperPurePartitioningCover fine coarserCoarse)
    (actualParent :
      Fin actualCoarse.card → Fin coarserCoarse.card)
    (compatible :
      ∀ source,
        actualParent (actualCover.parent source) =
          coarserCover.parent source)
    (actualScale_nonneg : 0 ≤ actual)
    (coarserScale_nonneg : 0 ≤ coarserScale)
    (parent :
      Fin (coarserCover.hitParentSubfamily
        data.selectedFine).family.card) :
    wz2PaperOrdinaryFullFiberCount
        data.selectedFine.family
        (coarserCover.hitParentSubfamily
          data.selectedFine).family parent =
      ∑ actual ∈ selectedActualParents.filter
          (fun current =>
            actualParent current =
              (coarserCover.hitParentSubfamily
                data.selectedFine).embedding parent),
        wz2PaperOrdinaryFullFiberCount
          fine actualCoarse actual := by
  let target :=
    (coarserCover.hitParentSubfamily
      data.selectedFine).embedding parent
  let selectedCoarserFiber :=
    (Finset.univ :
      Finset (Fin data.selectedFine.family.card)).filter fun source =>
        coarserCover.parent
            (data.selectedFine.embedding source) =
          target
  have selectedCount :
      wz2PaperOrdinaryFullFiberCount
          data.selectedFine.family
          (coarserCover.hitParentSubfamily
            data.selectedFine).family parent =
        (selectedCoarserFiber.card : ENNReal) := by
    rw [wz2PaperOrdinaryFullFiberCount]
    rw [
      coarserCover.restrictToHitParents_fullFiberIndices_eq
        coarserScale_nonneg data.selectedFine parent
    ]
  let ambientSelected :=
    data.selectedFineIndices.filter fun source =>
      coarserCover.parent source = target
  have imageSelected :
      Finset.image data.selectedFine.embedding
          selectedCoarserFiber =
        ambientSelected := by
    ext ambientSource
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨selectedSource, hselectedSource, rfl⟩
      have hparent :=
        (Finset.mem_filter.mp hselectedSource).2
      exact
        Finset.mem_filter.mpr
          ⟨data.selectedFine_embedding_mem selectedSource,
            hparent⟩
    · intro hsource
      have ambientMem :=
        (Finset.mem_filter.mp hsource).1
      have parentEq :=
        (Finset.mem_filter.mp hsource).2
      rcases
          data.selectedFine_ambient_surjective
            ambientSource ambientMem
        with
        ⟨selectedSource, hselectedSource⟩
      refine
        Finset.mem_image.mpr
          ⟨selectedSource, ?_, hselectedSource⟩
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ selectedSource,
            by rwa [hselectedSource]⟩
  have selectedCard :
      selectedCoarserFiber.card =
        ambientSelected.card := by
    rw [← imageSelected]
    exact
      Finset.card_image_of_injective _
        data.selectedFine.embedding.injective |>.symm
  have fiberwiseNat :
      ∑ actual ∈ selectedActualParents.filter
          (fun current => actualParent current = target),
          (Finset.univ.filter fun source =>
            actualCover.parent source = actual).card =
        ambientSelected.card := by
    let selectedParents :=
      selectedActualParents.filter fun current =>
        actualParent current = target
    have hsum :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        selectedParents actualCover.parent
    have hfilter :
        (Finset.univ.filter fun source =>
          actualCover.parent source ∈ selectedParents) =
          ambientSelected := by
      ext source
      simp only [selectedParents, ambientSelected,
        selectedFineIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hselected, htarget⟩
        exact ⟨hselected, by
          rw [← compatible source]
          exact htarget⟩
      · rintro ⟨hselected, htarget⟩
        exact ⟨hselected, by
          rw [compatible source]
          exact htarget⟩
    exact hsum.trans (congrArg Finset.card hfilter)
  rw [selectedCount, selectedCard]
  rw [show
    ∑ actual ∈ selectedActualParents.filter
        (fun current => actualParent current = target),
      wz2PaperOrdinaryFullFiberCount fine actualCoarse actual =
      ∑ actual ∈ selectedActualParents.filter
        (fun current => actualParent current = target),
        ((Finset.univ.filter fun source =>
          actualCover.parent source = actual).card : ENNReal) by
      apply Finset.sum_congr rfl
      intro actual _
      rw [wz2PaperOrdinaryFullFiberCount]
      have hindices :
          wz2PaperOrdinaryFullFiberIndices
              fine actualCoarse actual =
            Finset.univ.filter fun source =>
              actualCover.parent source = actual := by
        ext source
        rw [actualCover.mem_fullFiber_iff_parent_eq
          actualScale_nonneg actual source]
        simp
      rw [hindices]]
  rw [← Nat.cast_sum]
  exact_mod_cast fiberwiseNat.symm

/--
Coarser restricted fibers are `ambientConstant * degreeConstant`-uniform when
selected actual-parent class counts are `degreeConstant`-uniform.
-/
theorem coarser_restricted_fullFiber_uniform
    {delta actual coarserScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualCoarse :
      Kakeya.Streamlined.TubeFamily actual}
    {coarserCoarse :
      Kakeya.Streamlined.TubeFamily coarserScale}
    {actualCover :
      WZ2PaperPurePartitioningCover fine actualCoarse}
    {selectedActualParents :
      Finset (Fin actualCoarse.card)}
    (data :
      PureWZ2CompleteParentRestrictionData
        actualCover selectedActualParents)
    (coarserCover :
      WZ2PaperPurePartitioningCover fine coarserCoarse)
    (actualParent :
      Fin actualCoarse.card → Fin coarserCoarse.card)
    (compatible :
      ∀ source,
        actualParent (actualCover.parent source) =
          coarserCover.parent source)
    (actualScale_nonneg : 0 ≤ actual)
    (coarserScale_nonneg : 0 ≤ coarserScale)
    {ambientConstant degreeConstant : ENNReal}
    (actualUniform :
      WZ2PaperPureFullFibersAreCUniform
        fine actualCoarse ambientConstant)
    (degreeUniform :
      ∀ first second,
        0 <
            (selectedActualParents.filter fun actual =>
              actualParent actual = first).card →
        0 <
            (selectedActualParents.filter fun actual =>
              actualParent actual = second).card →
        ((selectedActualParents.filter fun actual =>
          actualParent actual = first).card : ENNReal) ≤
          degreeConstant *
            ((selectedActualParents.filter fun actual =>
              actualParent actual = second).card : ENNReal)) :
    WZ2PaperPureFullFibersAreCUniform
      data.selectedFine.family
      (coarserCover.hitParentSubfamily
        data.selectedFine).family
      (ambientConstant * degreeConstant) := by
  intro first second
  rw [
    data.coarser_restricted_fullFiberCount_eq_selected_actual_sum
      coarserCover actualParent compatible actualScale_nonneg
      coarserScale_nonneg first,
    data.coarser_restricted_fullFiberCount_eq_selected_actual_sum
      coarserCover actualParent compatible actualScale_nonneg
      coarserScale_nonneg second
  ]
  let firstAmbient :=
    (coarserCover.hitParentSubfamily
      data.selectedFine).embedding first
  let secondAmbient :=
    (coarserCover.hitParentSubfamily
      data.selectedFine).embedding second
  have firstPos :
      0 <
        (selectedActualParents.filter fun actual =>
          actualParent actual = firstAmbient).card := by
    rcases
        coarserCover.hitParent_surjective
          data.selectedFine first
      with
      ⟨source, hsource⟩
    have actualMem := data.selectedFine_parent_mem source
    refine Finset.card_pos.mpr
      ⟨actualCover.parent (data.selectedFine.embedding source),
        Finset.mem_filter.mpr
          ⟨actualMem, ?_⟩⟩
    rw [compatible,
      ← coarserCover.hitParent_ambient
        data.selectedFine source, hsource]
  have secondPos :
      0 <
        (selectedActualParents.filter fun actual =>
          actualParent actual = secondAmbient).card := by
    rcases
        coarserCover.hitParent_surjective
          data.selectedFine second
      with
      ⟨source, hsource⟩
    have actualMem := data.selectedFine_parent_mem source
    refine Finset.card_pos.mpr
      ⟨actualCover.parent (data.selectedFine.embedding source),
        Finset.mem_filter.mpr
          ⟨actualMem, ?_⟩⟩
    rw [compatible,
      ← coarserCover.hitParent_ambient
        data.selectedFine source, hsource]
  exact
    wz2_uniform_selected_class_weight
      (fun actual =>
        wz2PaperOrdinaryFullFiberCount
          fine actualCoarse actual)
      ambientConstant actualUniform
      selectedActualParents actualParent
      degreeConstant degreeUniform
      firstAmbient secondAmbient firstPos secondPos

end PureWZ2CompleteParentRestrictionData

end Kakeya.Assouad

end
