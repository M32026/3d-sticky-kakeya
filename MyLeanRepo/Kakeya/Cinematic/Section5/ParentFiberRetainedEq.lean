import MyLeanRepo.Kakeya.Cinematic.Section5.ParentFiberCardinalityRegularizationInputs

/-!
# Parent-fiber equality for retained rectangles

When a coarse parent belongs to the selected parent set, restricting rectangles
to those over selected parents does not change that parent's fiber.
-/

namespace Kakeya.Cinematic

lemma parentFiber_retained_eq
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (rectangles : Finset β) (parent : β → γ)
    (selectedParents : Finset γ) (coarse : γ)
    (hcoarse : coarse ∈ selectedParents) :
    parentFiber
      (rectanglesOverParents rectangles parent selectedParents)
      parent coarse =
    parentFiber rectangles parent coarse := by
  ext rectangle
  simp only [parentFiber, rectanglesOverParents, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hrectangle, _⟩, hparent⟩
    exact ⟨hrectangle, hparent⟩
  · rintro ⟨hrectangle, hparent⟩
    refine ⟨⟨hrectangle, ?_⟩, hparent⟩
    rw [hparent]
    exact hcoarse

end Kakeya.Cinematic
