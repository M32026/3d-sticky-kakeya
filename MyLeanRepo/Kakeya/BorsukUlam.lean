import MyLeanRepo.Kakeya.BorsukUlam.DegreeProof

/-!
# Borsuk--Ulam theorem

Adapted from an upstream mathlib extension, commit `e9ffbee0d0cb6b99dfab40c218df014f44d026bf`.
-/

namespace TopCat

/-- The antipodal map on `TopCat.sphere`. -/
def sphereAntipodal (n : ℕ) (x : 𝕊 n) : 𝕊 n :=
  ULift.up ⟨-x.down.1, by simp⟩

end TopCat

open TopCat

/-- Borsuk-Ulam theorem. -/
theorem borsuk_ulam {n j : ℕ} (hjn : j ≤ n)
    (f : 𝕊 n → EuclideanSpace ℝ (Fin j)) (hf_cont : Continuous f)
    (hf_odd : ∀ x, f (sphereAntipodal n x) = -f x) :
    0 ∈ Set.range f := by
  have h_antipodal : sphereAntipodal n = BorsukUlam.sphereAntipodal n := by
    funext x
    simp [sphereAntipodal, BorsukUlam.sphereAntipodal]
  have hf_odd' : ∀ x, f (BorsukUlam.sphereAntipodal n x) = -f x := by
    rw [h_antipodal] at hf_odd
    exact hf_odd
  exact BorsukUlam.DegreeProof.borsuk_ulam_full hjn f hf_cont hf_odd'

