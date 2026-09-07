import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicRepresentativeInputs

/-!
# Dyadic upper representative comparability
-/

namespace Kakeya.Cinematic

theorem dyadic_upper_representative :
    DyadicUpperRepresentativeStatement := by
  intro delta x N k hdelta hx _ hbound hmin
  cases k with
  | zero =>
    have h : (2 : ℝ) ^ (0 + 1) * delta = 2 * delta := by ring
    rw [h]
    linarith
  | succ j =>
    have h_j : j < j + 1 := by omega
    have h1 : ¬ x ≤ (2 : ℝ) ^ (j + 1) * delta := hmin j h_j
    have h2 : (2 : ℝ) ^ (j + 1) * delta < x := by
      exact lt_of_not_ge h1
    have h3 :
        (2 : ℝ) ^ ((j + 1) + 1) * delta < 2 * x := by
      have h4 :
          (2 : ℝ) ^ ((j + 1) + 1) * delta =
            2 * ((2 : ℝ) ^ (j + 1) * delta) := by
        ring
      rw [h4]
      linarith
    exact h3.le

end Kakeya.Cinematic
