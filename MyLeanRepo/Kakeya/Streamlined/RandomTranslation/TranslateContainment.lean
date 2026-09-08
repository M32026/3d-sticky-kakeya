import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.GeometricProbability

/-!
# Translation containment equivalence

If translating a set by `v` lands it in `t`, then the original set lies in
the translate of `t` by `-v`, and conversely.
-/

noncomputable section

open Set

namespace Kakeya.Streamlined.RandomTranslation

lemma translateSet_subset_iff {s t : Set Point3} {v : Point3} :
    translateSet s v ⊆ t ↔ s ⊆ translateSet t (-v) := by
  constructor
  · intro h x hx
    have h1 : x + v ∈ translateSet s v := ⟨x, hx, by abel⟩
    have h2 : x + v ∈ t := h h1
    exact ⟨x + v, h2, by abel⟩
  · intro h y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases h hx with ⟨z, hz, hzx⟩
    have hxz : x + v = z := by
      calc
        x + v = (z + (-v)) + v := by
          rw [show x = z + (-v) from hzx.symm]
        _ = z := by abel
    change x + v ∈ t
    rw [hxz]
    exact hz

end Kakeya.Streamlined.RandomTranslation
