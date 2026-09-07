import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Extract finite covers from external covering number bounds

Bridge between `externalCoveringNumber` and explicit finite `Finset` covers.
-/

noncomputable section

namespace Kakeya.Assouad

open Set Metric

/--
If the external covering number is finite, there exists a finite set `C`
that is a minimal cover, with encard equal to the covering number.
-/
lemma exists_set_encard_eq_externalCoveringNumber
    {X : Type _} [PseudoMetricSpace X] {ε : NNReal} {A : Set X}
    (h : externalCoveringNumber ε A ≠ ⊤) :
    ∃ (C : Set X), C.Finite ∧ IsCover ε A C ∧ C.encard = externalCoveringNumber ε A := by
  simp only [externalCoveringNumber, ne_eq, iInf_eq_top, encard_eq_top_iff,
    not_forall, not_infinite] at h
  obtain ⟨C', hC'_cover, hC'_fin⟩ := h
  have h_nonempty : Nonempty { s : Set X // IsCover ε A s } :=
    ⟨⟨C', hC'_cover⟩⟩
  let h_exists := ENat.exists_eq_iInf
    (fun C : {s : Set X // IsCover ε A s} ↦ (C : Set X).encard)
  obtain ⟨C, hC⟩ := h_exists
  refine ⟨(C : Set X), ?_, C.property, ?_⟩
  · refine Set.encard_lt_top_iff.mp ?_
    simp only [hC, iInf_lt_top, encard_lt_top_iff, Subtype.exists, exists_prop]
    exact ⟨C', hC'_cover, hC'_fin⟩
  · have h_eq : (iInf (fun C : {s : Set X // IsCover ε A s} ↦ (C : Set X).encard)) =
        externalCoveringNumber ε A := by
      simp [externalCoveringNumber, iInf_subtype]
      <;> rfl
    rw [hC, h_eq]

/--
If the external covering number is finite, there exists a `Finset` cover
with cardinality equal to the covering number.
-/
lemma exists_finset_cover_of_externalCoveringNumber
    {X : Type _} [PseudoMetricSpace X] {ε : NNReal} {A : Set X}
    (h : externalCoveringNumber ε A ≠ ⊤) :
    ∃ (C : Finset X), IsCover ε A (C : Set X) ∧
      (C.card : ENat) = externalCoveringNumber ε A := by
  rcases exists_set_encard_eq_externalCoveringNumber h with ⟨S, hS_fin, hS_cover, hS_encard⟩
  let C : Finset X := hS_fin.toFinset
  have h1 : (C : Set X) = S := hS_fin.coe_toFinset
  refine ⟨C, ?_, ?_⟩
  · rw [h1]
    exact hS_cover
  · have h2 : (C.card : ENat) = S.encard := by
      have h3 : (C : Set X) = S := h1
      have h4 : (C : Set X).encard = (C.card : ENat) := Set.encard_coe_eq_coe_finsetCard C
      rw [← h4, h3]
    rw [h2, hS_encard]

end Kakeya.Assouad
