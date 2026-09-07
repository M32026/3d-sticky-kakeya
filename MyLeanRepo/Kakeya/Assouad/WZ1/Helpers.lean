import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import Mathlib.Tactic

/-!
# Finite ENNReal helper lemmas for WZ1
-/

namespace Kakeya.Assouad

open Finset

lemma finset_ennreal_pigeonhole
    {α : Type*} [DecidableEq α] {s : Finset α}
    (hs : s.Nonempty) (f : α → ENNReal) :
    ∃ i ∈ s,
      (s.card : ENNReal) * f i ≥ ∑ j ∈ s, f j := by
  let im : Finset ENNReal := s.image f
  have h_im_nonempty : im.Nonempty :=
    Finset.Nonempty.image hs f
  let M : ENNReal := im.max' h_im_nonempty
  have hM_mem : M ∈ im :=
    Finset.max'_mem im h_im_nonempty
  rcases Finset.mem_image.mp hM_mem with
    ⟨i, hi, hfi⟩
  have h_le : ∀ j ∈ s, f j ≤ f i := by
    intro j hj
    have h1 : f j ∈ im :=
      Finset.mem_image_of_mem f hj
    have h2 : f j ≤ M :=
      Finset.le_max' im (f j) h1
    rw [hfi] at *
    exact h2
  have h_sum :
      ∑ j ∈ s, f j ≤ ∑ _j ∈ s, f i :=
    Finset.sum_le_sum h_le
  have h_final :
      ∑ j ∈ s, f j ≤ (s.card : ENNReal) * f i := by
    simpa [Finset.sum_const] using h_sum
  exact ⟨i, hi, h_final⟩

end Kakeya.Assouad
