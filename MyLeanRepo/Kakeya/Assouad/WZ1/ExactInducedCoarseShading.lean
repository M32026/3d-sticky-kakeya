import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic

/-!
# Exact induced coarse shading construction

Given a fine shading and a coherent cover at scale `rho`, construct the exact
induced coarse shading as the intersection of each coarse tube carrier with the
`rho`-thickening of the corresponding fine shaded fiber union.

This is the canonical construction used by WZ1 Proposition 5 to obtain the
coarse shading from the balanced cover's refined fine shading.
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

/--
Construct the exact induced coarse shading from a fine shading and a coherent cover.

For each coarse index `j`, the carrier is:
`(coarse.tube j).carrier ∩ cthickening rho {p | ∃ i, parent i = j ∧ p ∈ refined.carrier i}`
-/
def exactInducedCoarseShading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (refined : Kakeya.Streamlined.TubeShading F) :
    Kakeya.Streamlined.TubeShading (U.coarse rho) :=
  let cover := U.cover rho
  let coarse := U.coarse rho
  { carrier := fun j : Fin coarse.card =>
      (coarse.tube j).carrier ∩
      Metric.cthickening rho.1
        {p : Point3 | ∃ i : Fin F.card, cover.parent i = j ∧ p ∈ refined.carrier i}
    measurable_carrier := by
      intro j
      exact Metric.isClosed_cthickening.measurableSet.inter
        Metric.isClosed_cthickening.measurableSet
    subset_body := by
      intro j
      exact Set.inter_subset_left }

/-- The exact induced coarse shading satisfies `IsExactInducedShading`. -/
lemma exactInducedCoarseShading_isExact
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (refined : Kakeya.Streamlined.TubeShading F) :
    (U.cover rho).toFactoring.IsExactInducedShading
      refined (exactInducedCoarseShading U rho refined) rho.1 := by
  intro j
  rfl

/-- The exact induced coarse shading satisfies `IsInducedSubshading`. -/
lemma exactInducedCoarseShading_isInducedSubshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (refined : Kakeya.Streamlined.TubeShading F) :
    (U.cover rho).toFactoring.IsInducedSubshading
      refined (exactInducedCoarseShading U rho refined) rho.1 := by
  intro j
  exact Set.Subset.refl _

/--
Point compatibility: every point in a fine carrier lies in the corresponding
coarse carrier of the induced shading.
-/
lemma exactInducedCoarseShading_pointCompatibility
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (refined : Kakeya.Streamlined.TubeShading F) :
    ∀ (i : Fin F.card) (p : Point3),
      p ∈ refined.carrier i →
        p ∈ (exactInducedCoarseShading U rho refined).carrier
          ((U.cover rho).parent i) := by
  intro i p hp
  let cover := U.cover rho
  let j := cover.parent i
  let coarse := U.coarse rho
  have h1 : p ∈ (coarse.tube j).carrier :=
    cover.nested i (refined.subset_body i hp)
  let S : Set Point3 :=
    {p : Point3 | ∃ i' : Fin F.card, cover.parent i' = j ∧ p ∈ refined.carrier i'}
  have h2 : p ∈ S := ⟨i, rfl, hp⟩
  have h3 : p ∈ Metric.cthickening rho.1 S :=
    Metric.self_subset_cthickening S h2
  exact ⟨h1, h3⟩

/--
If the fine shaded union is nonempty, the coarse shaded union is nonempty.
-/
lemma exactInducedCoarseShading_nonempty
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (refined : Kakeya.Streamlined.TubeShading F)
    (h : refined.union.Nonempty) :
    (exactInducedCoarseShading U rho refined).union.Nonempty := by
  rcases h with ⟨p, hp⟩
  rcases hp with ⟨i, hi⟩
  have h4 : p ∈ (exactInducedCoarseShading U rho refined).carrier
      ((U.cover rho).parent i) :=
    exactInducedCoarseShading_pointCompatibility U rho refined i p hi
  refine ⟨p, ?_⟩
  exact ⟨(U.cover rho).parent i, h4⟩

end Kakeya.Assouad
