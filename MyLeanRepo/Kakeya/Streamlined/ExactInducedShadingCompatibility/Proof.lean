import MyLeanRepo.Kakeya.Streamlined.ExactInducedShadingCompatibility

/-!
# Compatibility of the exact induced shading
-/

namespace Kakeya.Streamlined

theorem exact_induced_shading_compatibility_main :
    ExactInducedShadingCompatibilityStatement := by
  intro fine coarse P Y Z r h
  have h1 : ∀ x ∈ Y.union, ∀ i, x ∈ Y.carrier i → x ∈ Z.carrier (P.parent i) := by
    intro x _ i hxi
    set j : Fin coarse.card := P.parent i with hj
    have h2 : x ∈ (coarse.body j).carrier := by
      have h21 : x ∈ (fine.body i).carrier := Y.subset_body i hxi
      exact P.contained i h21
    let S : Set Point3 := {x | ∃ i' : Fin fine.card, P.parent i' = j ∧ x ∈ Y.carrier i'}
    have h3 : x ∈ S := by
      exact ⟨i, by simp [hj], hxi⟩
    have h4 : x ∈ Metric.cthickening r S := Metric.self_subset_cthickening S h3
    have h5 : Z.carrier j = (coarse.body j).carrier ∩ Metric.cthickening r S := h j
    rw [h5]
    exact ⟨h2, h4⟩
  have h6 : Y.union ⊆ Z.union :=
    factoring_shading_union_compatibility_main P Y Z h1
  exact ⟨h1, h6⟩

end Kakeya.Streamlined
