import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Hit-parent restriction of a WZ line cover

Restrict a `WZ1PaperTubeCover` to a fine subfamily and exactly the caller
parents still hit by that subfamily.  This is the line-metric analogue of the
existing pure and internal hit-parent restrictions.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace WZ1PaperTubeCover

/-- Ambient caller indices hit by a selected fine subfamily. -/
def hitParentIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Finset (Fin coarse.card) :=
  Finset.univ.image fun source =>
    cover.parent (selected.embedding source)

/-- Caller subfamily consisting exactly of hit parents. -/
noncomputable def hitParentSubfamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Kakeya.Streamlined.TubeSubfamily coarse :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    coarse (cover.hitParentIndices selected)

/-- Hit-parent index of one selected fine tube. -/
noncomputable def hitParent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Fin selected.family.card →
      Fin (cover.hitParentSubfamily selected).family.card :=
  fun source =>
    let parents := cover.hitParentIndices selected
    let equivalence : Fin parents.card ≃ parents :=
      (parents.orderIsoOfFin rfl).toEquiv
    equivalence.symm
      ⟨cover.parent (selected.embedding source), by
        exact
          Finset.mem_image.mpr
            ⟨source, Finset.mem_univ source, rfl⟩⟩

@[simp] theorem hitParent_ambient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (source : Fin selected.family.card) :
    (cover.hitParentSubfamily selected).embedding
        (cover.hitParent selected source) =
      cover.parent (selected.embedding source) := by
  let parents := cover.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  change
    (parents.orderEmbOfFin rfl)
        (equivalence.symm
          ⟨cover.parent (selected.embedding source), _⟩) =
      cover.parent (selected.embedding source)
  exact
    congrArg Subtype.val
      (equivalence.apply_symm_apply
        ⟨cover.parent (selected.embedding source), by
          exact
            Finset.mem_image.mpr
              ⟨source, Finset.mem_univ source, rfl⟩⟩)

theorem hitParent_surjective
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Function.Surjective (cover.hitParent selected) := by
  intro parent
  have parentMem :
      (cover.hitParentSubfamily selected).embedding parent ∈
        cover.hitParentIndices selected :=
    Finset.orderEmbOfFin_mem
      (cover.hitParentIndices selected) rfl parent
  rcases Finset.mem_image.mp parentMem with
    ⟨source, _, hsource⟩
  refine ⟨source, ?_⟩
  apply
    (cover.hitParentSubfamily selected).embedding.injective
  rw [cover.hitParent_ambient]
  exact hsource

/-- Restrict a WZ line cover to selected fine tubes and hit callers. -/
noncomputable def restrictToHitParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ1PaperTubeCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    WZ1PaperTubeCover
      selected.family
      (cover.hitParentSubfamily selected).family where
  parent := cover.hitParent selected
  parent_surjective := cover.hitParent_surjective selected
  parent_covers source := by
    rw [selected.tube_eq,
      (cover.hitParentSubfamily selected).tube_eq,
      cover.hitParent_ambient]
    exact cover.parent_covers (selected.embedding source)
  parent_unique source candidate hcandidate := by
    apply
      (cover.hitParentSubfamily selected).embedding.injective
    rw [cover.hitParent_ambient]
    apply cover.parent_unique (selected.embedding source)
    rw [← selected.tube_eq source,
      ← (cover.hitParentSubfamily selected).tube_eq candidate]
    exact hcandidate

end WZ1PaperTubeCover

end Kakeya.Assouad

end
