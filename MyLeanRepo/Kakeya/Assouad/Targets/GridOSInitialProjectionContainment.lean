import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSReadyStateStatements

/-!
WZ2 Theorem 5.2: transport the selected initial twisted projection into the
original source projection.
-/

namespace Kakeya.Assouad

theorem grid_os_initial_projection_containment :
    GridOSInitialProjectionContainmentStatement := by
  intro delta eta family shading sourceConstant initial f
  let selected := initial.uniform.selected
  let pruned := initial.pruned
  have h_main : ∀ (F' : Kakeya.Streamlined.TubeFamily delta)
      (Y' : Kakeya.Streamlined.TubeShading F')
      (hF : F' = selectedTubeFamily family selected)
      (hY : HEq Y' (selectedTubeShading pruned selected)),
      twistedUnion Y' f ⊆ twistedUnion shading f := by
    intro F' Y' hF hY
    subst hF
    have hY' : Y' = selectedTubeShading pruned selected := by
      cases hY
      rfl
    rw [hY']
    have h1 : (selectedTubeShading pruned selected).union ⊆ pruned.union :=
      selectedTubeShading_union_subset pruned selected
    have h2 : pruned.union ⊆ shading.union :=
      initial.pruned_subshading.union_subset
    have h3 : (selectedTubeShading pruned selected).union ⊆ shading.union :=
      h1.trans h2
    have h4 : twistedProjection f '' (selectedTubeShading pruned selected).union ⊆
        twistedProjection f '' shading.union := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      exact ⟨y, h3 hy, rfl⟩
    simpa [twistedUnion] using h4
  exact h_main initial.selectedFamily initial.selectedShading
    initial.selectedFamily_eq initial.selectedShading_eq

end Kakeya.Assouad
