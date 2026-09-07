import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperParentCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.WZLineCoverHitRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Proposition 6.2 metric parents: restriction to the final tree core

Restrict the metric parent cover to the final leaf core and exactly the
parents still hit by that core.  The restricted metric fibers are precisely
the core intersections of the original complete metric fibers.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62MetricCoreRestrictionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (ambient : PureWZ2Section6Cover fine coarse)
    (core : Finset (Fin fine.card)) where
  core_nonempty : core.Nonempty
  fineSelected : Kakeya.Streamlined.TubeSubfamily fine
  fineSelected_eq :
    fineSelected =
      Kakeya.Streamlined.TubeSubfamily.fromFinset fine core
  coarseSelected : Kakeya.Streamlined.TubeSubfamily coarse
  lineCover :
    WZ1PaperTubeCover
      fineSelected.family coarseSelected.family
  section6Cover :
    PureWZ2Section6Cover
      fineSelected.family coarseSelected.family
  fine_image_univ :
    Finset.image fineSelected.embedding Finset.univ = core
  fiber_image_eq :
    ∀ parent,
      Finset.image fineSelected.embedding
          (wz2PaperFullFiberIndices
            fineSelected.family coarseSelected.family parent) =
        core ∩
          wz2PaperFullFiberIndices
            fine coarse (coarseSelected.embedding parent)

theorem pureWZ2_prop62_metric_core_restriction
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (ambient : PureWZ2Section6Cover fine coarse)
    (core : Finset (Fin fine.card))
    (coreNonempty : core.Nonempty) :
    Nonempty
      (PureWZ2Prop62MetricCoreRestrictionData ambient core) := by
  let ambientLine := ambient.toWZ1PaperTubeCover
  let fineSelected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset fine core
  let coarseSelected :=
    ambientLine.hitParentSubfamily fineSelected
  let lineCover :=
    ambientLine.restrictToHitParents fineSelected
  have fineImage :
      Finset.image fineSelected.embedding Finset.univ = core := by
    ext source
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨index, _, rfl⟩
      exact Finset.orderEmbOfFin_mem core rfl index
    · intro hsource
      let equivalence : Fin core.card ≃ core :=
        (core.orderIsoOfFin rfl).toEquiv
      refine Finset.mem_image.mpr
        ⟨equivalence.symm ⟨source, hsource⟩,
          Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val
        (equivalence.apply_symm_apply ⟨source, hsource⟩)
  let section6 :
      PureWZ2Section6Cover
        fineSelected.family coarseSelected.family :=
    {
      fine_line_class :=
        ambient.fine_line_class.subfamily fineSelected
      coarse_line_class :=
        ambient.coarse_line_class.subfamily coarseSelected
      covers := fun source =>
        ⟨lineCover.parent source,
          lineCover.parent_covers source⟩
      parent_hit := by
        intro parent
        rcases lineCover.parent_surjective parent with
          ⟨source, hsource⟩
        exact
          ⟨source, hsource ▸ lineCover.parent_covers source⟩
      coarse_essentially_distinct :=
        ambient.coarse_essentially_distinct.subfamily
          coarseSelected
    }
  have fiberImage :
      ∀ parent,
        Finset.image fineSelected.embedding
            (wz2PaperFullFiberIndices
              fineSelected.family coarseSelected.family parent) =
          core ∩
            wz2PaperFullFiberIndices
              fine coarse (coarseSelected.embedding parent) := by
    intro parent
    ext ambientSource
    constructor
    · intro hsource
      rcases Finset.mem_image.mp hsource with
        ⟨source, hsourceFiber, rfl⟩
      have hcore :
          fineSelected.embedding source ∈ core := by
        rw [← fineImage]
        exact Finset.mem_image.mpr
          ⟨source, Finset.mem_univ source, rfl⟩
      have hcovered :
          WZ1PaperTubeCovers
            (fineSelected.family.tube source)
            (coarseSelected.family.tube parent) :=
        (mem_wz2PaperFullFiberIndices_iff parent source).mp
          hsourceFiber
      exact Finset.mem_inter.mpr
        ⟨hcore,
          (mem_wz2PaperFullFiberIndices_iff
            (coarseSelected.embedding parent)
            (fineSelected.embedding source)).mpr <| by
            simpa only [fineSelected.tube_eq,
              coarseSelected.tube_eq] using hcovered⟩
    · intro hsource
      have hdata := Finset.mem_inter.mp hsource
      have hselected :
          ambientSource ∈
            Finset.image fineSelected.embedding Finset.univ := by
        rw [fineImage]
        exact hdata.1
      rcases Finset.mem_image.mp hselected with
        ⟨source, _, hsourceEq⟩
      refine Finset.mem_image.mpr
        ⟨source, ?_, hsourceEq⟩
      rw [mem_wz2PaperFullFiberIndices_iff]
      have hcovered :
          WZ1PaperTubeCovers
            (fine.tube ambientSource)
            (coarse.tube (coarseSelected.embedding parent)) :=
        (mem_wz2PaperFullFiberIndices_iff
          (coarseSelected.embedding parent) ambientSource).mp hdata.2
      rw [← hsourceEq] at hcovered
      simpa only [fineSelected.tube_eq,
        coarseSelected.tube_eq] using hcovered
  exact
    ⟨{
      core_nonempty := coreNonempty
      fineSelected := fineSelected
      fineSelected_eq := rfl
      coarseSelected := coarseSelected
      lineCover := lineCover
      section6Cover := section6
      fine_image_univ := fineImage
      fiber_image_eq := fiberImage
    }⟩

end Kakeya.Assouad

end
