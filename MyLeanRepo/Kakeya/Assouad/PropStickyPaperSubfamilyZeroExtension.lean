import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtensionStatements

/-!
# Extend a selected paper shading by zero

Define the ambient carrier as the finite union over selected indices whose
embedding equals the ambient index, then prove exact support, mass, union,
and cubicality.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_subfamily_zero_extension :
    WZ2PaperSubfamilyZeroExtensionStatement := by
  intro delta family selected shading
  let selectedIndicesFor (a : Fin family.card) : Finset (Fin selected.family.card) :=
    Finset.univ.filter (fun i => selected.embedding i = a)
  let ambientCarrier (a : Fin family.card) : Set Point3 :=
    ⋃ i ∈ selectedIndicesFor a, shading.carrier i
  have h_selected_indices : ∀ (i : Fin selected.family.card),
      selectedIndicesFor (selected.embedding i) = {i} := by
    intro i
    ext j
    simp [selectedIndicesFor, selected.embedding.injective.eq_iff]
  have h_not_in_image : ∀ (a : Fin family.card),
      a ∉ Finset.image selected.embedding Finset.univ →
      selectedIndicesFor a = ∅ := by
    intro a ha
    ext j
    simp [selectedIndicesFor, Finset.mem_image] at ha ⊢
    exact ha j
  have h_ambient_carrier_embedding : ∀ (i : Fin selected.family.card),
      ambientCarrier (selected.embedding i) = shading.carrier i := by
    intro i
    have h : ambientCarrier (selected.embedding i) =
        (⋃ j ∈ selectedIndicesFor (selected.embedding i), shading.carrier j) := rfl
    rw [h, h_selected_indices i]
    simp
  have h_ambient_carrier_empty : ∀ (a : Fin family.card),
      a ∉ Finset.image selected.embedding Finset.univ →
      ambientCarrier a = ∅ := by
    intro a ha
    have h : ambientCarrier a =
        (⋃ i ∈ selectedIndicesFor a, shading.carrier i) := rfl
    rw [h, h_not_in_image a ha]
    simp
  let ambientShading : WZ1PaperTubeShading family :=
    { carrier := ambientCarrier
      measurable_carrier := by
        intro a
        exact MeasurableSet.biUnion (Finset.finite_toSet (selectedIndicesFor a)).countable
          (fun i _ => shading.measurable_carrier i)
      subset_body := by
        intro a
        by_cases h : a ∈ Finset.image selected.embedding Finset.univ
        · rcases Finset.mem_image.mp h with ⟨i, _, rfl⟩
          rw [h_ambient_carrier_embedding i]
          have h_sub : shading.carrier i ⊆
              wz1PaperTubeCarrier (selected.family.tube i) :=
            shading.subset_body i
          have h_tube : selected.family.tube i =
              family.tube (selected.embedding i) := selected.tube_eq i
          rw [h_tube] at h_sub
          exact h_sub
        · rw [h_ambient_carrier_empty a h]
          exact Set.empty_subset _ }
  have h_carrier_support : ∀ (ambient : Fin family.card) (point : Point3),
      point ∈ ambientShading.carrier ambient →
        ∃ (index : Fin selected.family.card),
          selected.embedding index = ambient ∧ point ∈ shading.carrier index := by
    intro ambient point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨i, hi, hmem⟩
    have h_eq : selected.embedding i = ambient := by
      simpa [selectedIndicesFor, Finset.mem_filter] using hi
    exact ⟨i, h_eq, hmem⟩
  have h_image_sum : ∑ a ∈ Finset.image selected.embedding Finset.univ,
        MeasureTheory.volume (ambientCarrier a) =
      ∑ i : Fin selected.family.card, MeasureTheory.volume (shading.carrier i) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      rw [h_ambient_carrier_embedding i]
    · intro i _ j _ h
      exact selected.embedding.injective h
  have h_all_sum : ∑ a : Fin family.card, MeasureTheory.volume (ambientCarrier a) =
      ∑ a ∈ Finset.image selected.embedding Finset.univ, MeasureTheory.volume (ambientCarrier a) := by
    have h_sum : ∑ a ∈ Finset.image selected.embedding Finset.univ, MeasureTheory.volume (ambientCarrier a) =
        ∑ a : Fin family.card, MeasureTheory.volume (ambientCarrier a) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ hnot
      rw [h_ambient_carrier_empty a hnot]
      simp
    exact h_sum.symm
  have h_mass_eq : ambientShading.mass = shading.mass := by
    calc
      ambientShading.mass
        = ∑ a : Fin family.card, MeasureTheory.volume (ambientCarrier a) := by rfl
      _ = ∑ a ∈ Finset.image selected.embedding Finset.univ, MeasureTheory.volume (ambientCarrier a) := h_all_sum
      _ = ∑ i : Fin selected.family.card, MeasureTheory.volume (shading.carrier i) := h_image_sum
      _ = shading.mass := by rfl
  have h_union_eq : ambientShading.union = shading.union := by
    ext point
    constructor
    · rintro ⟨a, ha⟩
      rcases Set.mem_iUnion₂.mp ha with ⟨i, _, hmem⟩
      exact ⟨i, hmem⟩
    · rintro ⟨i, hmem⟩
      refine ⟨selected.embedding i, ?_⟩
      have h : ambientShading.carrier (selected.embedding i) = shading.carrier i :=
        h_ambient_carrier_embedding i
      rw [h]
      exact hmem
  have h_cubical : WZ1PaperIsCubicalShading shading →
      WZ1PaperIsCubicalShading ambientShading := by
    intro hcubical a point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨i, hi, hmem⟩
    have h_eq : selected.embedding i = a := by
      simpa [selectedIndicesFor, Finset.mem_filter] using hi
    have h_cube : wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        shading.carrier i := hcubical i point hmem
    have h_carrier_eq : ambientShading.carrier a = shading.carrier i := by
      have h9 : a = selected.embedding i := h_eq.symm
      have h10 : ambientShading.carrier a = ambientShading.carrier (selected.embedding i) := by
        exact congrArg ambientShading.carrier h9
      rw [h10]
      exact h_ambient_carrier_embedding i
    rw [h_carrier_eq]
    exact h_cube
  exact ⟨ambientShading, h_ambient_carrier_embedding, h_carrier_support,
    h_mass_eq, h_union_eq, h_cubical⟩

end Kakeya.Assouad

end
