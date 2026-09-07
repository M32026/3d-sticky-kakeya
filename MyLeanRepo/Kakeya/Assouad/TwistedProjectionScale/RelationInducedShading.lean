import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.FixedBlockFamily
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Relation-induced coarse shadings

Construct the exact windowed induced shading for a relation-valued block
cover.  This module is purely measurable/geometric; it does not assert a
density lower bound.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Exact coarse shading induced by a fine--coarse relation. -/
def relationInducedShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (Rel : Fin fine.card → Fin coarse.card → Prop)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) :
    Kakeya.Streamlined.TubeShading coarse where
  carrier j :=
    (coarse.tube j).carrier ∩ horizontalSlab (-1) 1 ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card, Rel i j ∧ x ∈ Y.carrier i}
  measurable_carrier j :=
    ((Metric.isClosed_cthickening.measurableSet.inter
      (measurableSet_horizontalSlab (-1) 1)).inter
        Metric.isClosed_cthickening.measurableSet)
  subset_body j := by
    intro point hpoint
    exact hpoint.1.1

lemma relationInducedShading_carrier
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (Rel : Fin fine.card → Fin coarse.card → Prop)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) (j : Fin coarse.card) :
    (relationInducedShading Rel Y r).carrier j =
      (coarse.tube j).carrier ∩ horizontalSlab (-1) 1 ∩
        Metric.cthickening r
          {x | ∃ i : Fin fine.card, Rel i j ∧ x ∈ Y.carrier i} := rfl

/-- The constructed shading satisfies the frozen exact relation predicate. -/
lemma relationInducedShading_exact
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (Rel : Fin fine.card → Fin coarse.card → Prop)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) :
    IsWindowedExactRelationInducedShading
      Rel Y (relationInducedShading Rel Y r) r := by
  intro j
  rfl

/-- The exact relation-induced shading stays in the slope window. -/
lemma relationInducedShading_slopeWindow
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (Rel : Fin fine.card → Fin coarse.card → Prop)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) :
    IsInSlopeWindow (relationInducedShading Rel Y r) := by
  intro point hpoint
  rcases hpoint with ⟨j, hj⟩
  exact hj.1.2

/-- Every coarse shaded point lies in the thickening of the fine shaded union. -/
lemma relationInducedShading_union_subset_thickening
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (Rel : Fin fine.card → Fin coarse.card → Prop)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) :
    (relationInducedShading Rel Y r).union ⊆
      Metric.cthickening r Y.union := by
  intro point hpoint
  rcases hpoint with ⟨j, hj⟩
  have hthick := hj.2
  apply Metric.cthickening_subset_of_subset r _ hthick
  intro x hx
  rcases hx with ⟨i, _, hxi⟩
  exact ⟨i, hxi⟩

/--
If every fine shaded point lies in a related coarse carrier, the fine shaded
union is contained in the exact relation-induced coarse shading.
-/
lemma fine_union_subset_relationInducedShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (Rel : Fin fine.card → Fin coarse.card → Prop)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) (hr : 0 ≤ r)
    (hwindow : IsInSlopeWindow Y)
    (hcover :
      ∀ i, ∀ point ∈ Y.carrier i,
        ∃ j, Rel i j ∧ point ∈ (coarse.tube j).carrier) :
    Y.union ⊆ (relationInducedShading Rel Y r).union := by
  intro point hpoint
  rcases hpoint with ⟨i, hi⟩
  rcases hcover i point hi with ⟨j, hrel, hj⟩
  refine ⟨j, ⟨⟨hj, hwindow ⟨i, hi⟩⟩, ?_⟩⟩
  exact Metric.self_subset_cthickening
    (E := {x | ∃ k : Fin fine.card, Rel k j ∧ x ∈ Y.carrier k})
    ⟨i, hrel, hi⟩

/-- Selected four-block data supplies the required related carrier cover. -/
lemma selectedScaleFourBlock_fine_union_subset_induced
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) (hr : 0 ≤ r)
    (hwindow : IsInSlopeWindow Y) :
    Y.union ⊆
      (relationInducedShading data.relation Y r).union := by
  apply fine_union_subset_relationInducedShading
    data.relation Y r hr hwindow
  intro i point hpoint
  exact data.carrier_subset_relation_union i
    (Y.subset_body i hpoint)

end Kakeya.Assouad
