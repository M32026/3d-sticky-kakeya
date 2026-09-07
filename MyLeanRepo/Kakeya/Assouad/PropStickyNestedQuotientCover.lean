import MyLeanRepo.Kakeya.Assouad.PropStickyNestedQuotientCounting
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberTreeGeometry

/-! # Quotient cover induced by two nested exact covers -/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperNestedQuotientCoverData
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {middle : Kakeya.Streamlined.TubeFamily rho}
    {coarse : Kakeya.Streamlined.TubeFamily sigma}
    (middleCover : WZ2PaperPartitioningCover fine middle)
    (coarseCover : WZ2PaperPartitioningCover fine coarse)
    (C : ENNReal) where
  representative : Fin middle.card → Fin fine.card
  representative_parent :
    ∀ parent,
      middleCover.parent (representative parent) = parent
  parent : Fin middle.card → Fin coarse.card
  parent_eq :
    ∀ middleParent,
      parent middleParent =
        coarseCover.parent (representative middleParent)
  compatible :
    ∀ source,
      parent (middleCover.parent source) =
        coarseCover.parent source
  cover : WZ2PaperDilatedTubeCover 2 middle coarse
  cover_parent_eq : cover.parent = parent
  assigned_fiber_uniform :
    ∀ first second,
      cover.fiberCount first ≤
        C * C * cover.fiberCount second

theorem wz2_paper_nested_quotient_cover
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {middle : Kakeya.Streamlined.TubeFamily rho}
    {coarse : Kakeya.Streamlined.TubeFamily sigma}
    (middleCover : WZ2PaperPartitioningCover fine middle)
    (coarseCover : WZ2PaperPartitioningCover fine coarse)
    (hmiddle : middle.Nonempty)
    (hscale : rho ≤ sigma)
    (nested :
      ∀ first second : Fin fine.card,
        middleCover.parent first = middleCover.parent second →
          coarseCover.parent first = coarseCover.parent second)
    (C : ENNReal)
    (middle_uniform :
      ∀ first second,
        wz2PaperFullFiberCount fine middle first ≤
          C * wz2PaperFullFiberCount fine middle second)
    (coarse_uniform :
      ∀ first second,
        wz2PaperFullFiberCount fine coarse first ≤
          C * wz2PaperFullFiberCount fine coarse second) :
    Nonempty
      (WZ2PaperNestedQuotientCoverData
        middleCover coarseCover C) := by
  have representativeExists :
      ∀ parent : Fin middle.card,
        ∃ source,
          middleCover.parent source = parent :=
    middleCover.parent_surjective
  let representative : Fin middle.card → Fin fine.card :=
    fun parent => Classical.choose (representativeExists parent)
  have hRepresentative :
      ∀ parent,
        middleCover.parent (representative parent) = parent :=
    fun parent => Classical.choose_spec (representativeExists parent)
  let parent : Fin middle.card → Fin coarse.card :=
    fun middleParent =>
      coarseCover.parent (representative middleParent)
  have hCompatible :
      ∀ source,
        parent (middleCover.parent source) =
          coarseCover.parent source := by
    intro source
    apply nested
    exact hRepresentative (middleCover.parent source)
  have hParentSurjective : Function.Surjective parent := by
    intro coarseParent
    rcases coarseCover.parent_surjective coarseParent with
      ⟨source, hsource⟩
    refine ⟨middleCover.parent source, ?_⟩
    rw [hCompatible source, hsource]
  let quotientCover : WZ2PaperDilatedTubeCover 2 middle coarse :=
    { parent := parent
      parent_surjective := hParentSurjective
      parent_covers := by
        intro middleParent
        apply
          middleCover.parents_dilated_cover_of_common_source
            coarseCover hscale
            (representative middleParent)
            middleParent
            (parent middleParent)
        · exact hRepresentative middleParent
        · rfl }
  have hMiddleUniform :
      ∀ first second,
        (((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            middleCover.parent source = first).card : ENNReal) ≤
          C *
            (((Finset.univ : Finset (Fin fine.card)).filter fun source =>
              middleCover.parent source = second).card : ENNReal) := by
    intro first second
    have h := middle_uniform first second
    rw [middleCover.fullFiberCount_eq first,
      middleCover.fullFiberCount_eq second] at h
    simpa only [WZ1PaperTubeCover.fiberIndices] using h
  have hCoarseUniform :
      ∀ first second,
        (((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            coarseCover.parent source = first).card : ENNReal) ≤
          C *
            (((Finset.univ : Finset (Fin fine.card)).filter fun source =>
              coarseCover.parent source = second).card : ENNReal) := by
    intro first second
    have h := coarse_uniform first second
    rw [coarseCover.fullFiberCount_eq first,
      coarseCover.fullFiberCount_eq second] at h
    simpa only [WZ1PaperTubeCover.fiberIndices] using h
  letI : Nonempty (Fin middle.card) := by
    exact ⟨⟨0, hmiddle⟩⟩
  have hQuotientUniform :
      ∀ first second,
        (((Finset.univ : Finset (Fin middle.card)).filter fun current =>
            parent current = first).card : ENNReal) ≤
          C * C *
            (((Finset.univ : Finset (Fin middle.card)).filter fun current =>
              parent current = second).card : ENNReal) :=
    nested_quotient_parent_count_uniform_square
      middleCover.parent coarseCover.parent parent
      middleCover.parent_surjective hCompatible C
      hMiddleUniform hCoarseUniform
  exact
    ⟨{
      representative := representative
      representative_parent := hRepresentative
      parent := parent
      parent_eq := fun _ => rfl
      compatible := hCompatible
      cover := quotientCover
      cover_parent_eq := rfl
      assigned_fiber_uniform := by
        intro first second
        exact hQuotientUniform first second
    }⟩

end Kakeya.Assouad

end
