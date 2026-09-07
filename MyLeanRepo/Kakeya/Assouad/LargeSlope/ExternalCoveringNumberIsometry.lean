import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# External covering number invariance under surjective isometries

Mathlib provides the analogous fact for the internal covering number.  This
module records the external-covering version needed by the large-slope
projection argument.
-/

namespace Kakeya.Assouad

/-- The external covering number is invariant under a surjective isometry. -/
lemma Isometry.externalCoveringNumber_image
    {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    {f : X → Y} (hf : Isometry f) (hsurj : Function.Surjective f)
    {A : Set X} {ε : NNReal} :
    Metric.externalCoveringNumber ε (f '' A) =
      Metric.externalCoveringNumber ε A := by
  classical
  refine le_antisymm ?_ ?_
  · simp only [Metric.externalCoveringNumber, le_iInf_iff]
    intro C hC_cover
    have hcover_image := (hf.isCover_image_iff C).mpr hC_cover
    refine (iInf_le _ (f '' C)).trans ?_
    refine (iInf_le _ hcover_image).trans ?_
    exact Set.encard_image_le f C
  · simp only [Metric.externalCoveringNumber, le_iInf_iff]
    intro C hC_cover
    let C' : Set X := f ⁻¹' C
    have hcover_preimage :
        ∀ x ∈ A, ∃ z ∈ C', edist x z ≤ ε := by
      intro x hx
      have hfx : f x ∈ f '' A := ⟨x, hx, rfl⟩
      rcases hC_cover hfx with ⟨y, hy, hdist⟩
      rcases hsurj y with ⟨z, rfl⟩
      refine ⟨z, hy, ?_⟩
      have hedist :
          edist x z = edist (f x) (f z) :=
        (hf.edist_eq x z).symm
      rw [hedist]
      exact hdist
    refine (iInf_le _ C').trans ?_
    refine (iInf_le _ hcover_preimage).trans ?_
    have himage : f '' C' = C := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        rcases hsurj y with ⟨x, rfl⟩
        exact ⟨x, hy, rfl⟩
    rw [← himage, hf.injective.encard_image]

/-- External covering numbers on `ℝ` are invariant under translation. -/
lemma translation_externalCoveringNumber (c : ℝ) (A : Set ℝ) (ε : NNReal) :
    Metric.externalCoveringNumber ε ((fun t : ℝ => t - c) '' A) =
      Metric.externalCoveringNumber ε A := by
  have hisometry : Isometry (fun t : ℝ => t - c) :=
    isometry_add_right (-c)
  have hsurjective : Function.Surjective (fun t : ℝ => t - c) := by
    intro y
    exact ⟨y + c, by ring⟩
  exact Isometry.externalCoveringNumber_image
    hisometry hsurjective

end Kakeya.Assouad
