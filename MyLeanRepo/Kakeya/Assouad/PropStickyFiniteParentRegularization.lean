import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization

/-!
# Simultaneous finite parent-map regularization
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem restrictPaperShading_fromFinset_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (selected : Finset (Fin family.card)) :
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset family selected)
      shading).mass =
        ∑ index ∈ selected, volume (shading.carrier index) := by
  let equivalence : Fin selected.card ≃ selected :=
    (selected.orderIsoOfFin rfl).toEquiv
  calc
    (restrictPaperShading
      (Kakeya.Streamlined.TubeSubfamily.fromFinset family selected)
      shading).mass =
        ∑ index : Fin selected.card,
          volume
            (shading.carrier
              (selected.orderEmbOfFin rfl index)) := rfl
    _ =
        ∑ index : selected,
          volume (shading.carrier index.1) := by
      exact
        Fintype.sum_equiv equivalence
          (fun index : Fin selected.card =>
            volume
              (shading.carrier
                (selected.orderEmbOfFin rfl index)))
          (fun index : selected =>
            volume (shading.carrier index.1))
          (fun _ => rfl)
    _ =
        ∑ index ∈ selected,
          volume (shading.carrier index) := by
      exact
        Finset.sum_coe_sort selected
          (fun index => volume (shading.carrier index))

theorem wz2_prop_sticky_finite_parent_regularization :
    WZ2PropStickyFiniteParentRegularizationStatement := by
  intro delta family shading scaleCount Parent _ _ parent
  let weight : Fin family.card → ENNReal :=
    fun index => volume (shading.carrier index)
  rcases
      simultaneous_degree_regularization
        scaleCount Parent parent weight
    with
      ⟨selected, hdegree, hretained⟩
  refine ⟨{
    selected := selected
    degree_uniform := ?_
    retained_mass := ?_ }⟩
  · simpa using hdegree
  change
    (∑ index : Fin family.card,
        volume (shading.carrier index)) ≤
      (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (scaleCount + 1) *
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            family selected)
          shading).mass
  rw [restrictPaperShading_fromFinset_mass]
  simpa [weight] using hretained

end Kakeya.Assouad

end
