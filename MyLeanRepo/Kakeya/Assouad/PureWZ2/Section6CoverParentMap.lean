import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers

/-!
# Derived parent map for a Section 6 line cover

`PureWZ2Section6Cover` stores the paper-facing existential cover relation.
Its coarse essential distinctness makes every strict `rho / 2` parent unique.
This module packages the resulting canonical parent map without adding a new
geometric assumption.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

noncomputable def PureWZ2Section6Cover.toWZ1PaperTubeCover
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse) :
    WZ1PaperTubeCover fine coarse := by
  let parent : Fin fine.card → Fin coarse.card :=
    fun source => Classical.choose (cover.covers source)
  have parentCovers :
      ∀ source,
        WZ1PaperTubeCovers
          (fine.tube source) (coarse.tube (parent source)) :=
    fun source => Classical.choose_spec (cover.covers source)
  have parentUnique :
      ∀ source candidate,
        WZ1PaperTubeCovers
            (fine.tube source) (coarse.tube candidate) →
          candidate = parent source := by
    intro source candidate candidateCovers
    by_contra hne
    have separated :=
      cover.coarse_essentially_distinct
        candidate (parent source) hne
    have triangle :=
      wz1PaperLineDistance_triangle
        (coarse.tube candidate) (fine.tube source)
        (coarse.tube (parent source))
    have symmetry :
        wz1PaperLineDistance
            (coarse.tube candidate) (fine.tube source) =
          wz1PaperLineDistance
            (fine.tube source) (coarse.tube candidate) :=
      wz1PaperLineDistance_symm _ _
    rw [symmetry] at triangle
    unfold WZ1PaperTubeCovers at candidateCovers parentCovers
    exact
      (not_le_of_gt separated)
        (triangle.trans (by
          linarith [candidateCovers, parentCovers source]))
  have parentSurjective : Function.Surjective parent := by
    intro coarseIndex
    rcases cover.parent_hit coarseIndex with
      ⟨source, sourceCovers⟩
    exact ⟨source, (parentUnique source coarseIndex sourceCovers).symm⟩
  exact
    {
      parent := parent
      parent_surjective := parentSurjective
      parent_covers := parentCovers
      parent_unique := parentUnique
    }

@[simp] theorem PureWZ2Section6Cover.toWZ1PaperTubeCover_parent_covers
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (source : Fin fine.card) :
    WZ1PaperTubeCovers
      (fine.tube source)
      (coarse.tube (cover.toWZ1PaperTubeCover.parent source)) :=
  cover.toWZ1PaperTubeCover.parent_covers source

end Kakeya.Assouad

end
