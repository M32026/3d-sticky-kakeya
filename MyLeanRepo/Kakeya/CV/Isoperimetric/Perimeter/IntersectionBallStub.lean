import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.IntersectionBall
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import Mathlib.Tactic

/-!
# Intersection Ball Perimeter Formula (RE-EXPORT)

Re-exports `perimeter_inter_ball_le_n_ge_two` as `perimeter_inter_ball_le`
for backward compatibility.
-/

open scoped MeasureTheory

open MeasureTheory ENNReal Metric

namespace Geometry.Perimeter

/-- **Intersection ball perimeter formula** (Maggi 15.12).

For a measurable set `S` and `x₀`, for a.e. `r > 0`:
`P(S ∩ B(x₀, r)) ≤ P(S; B(x₀, r)) + μHE[n-1](S ∩ ∂B(x₀, r))`. -/
lemma perimeter_inter_ball_le
    {n : ℕ} [Nonempty (Fin n)] (hn : 2 ≤ n)
    {S : Set (E n)} (hS : MeasurableSet S) (x₀ : E n) :
    ∀ᵐ (r : ℝ) ∂volume.restrict (Set.Ioi 0),
      perimeter (S ∩ ball x₀ r) ≤
        perimeterIn S (ball x₀ r) + μHE[n - 1] (S ∩ sphere x₀ r) :=
  perimeter_inter_ball_le_n_ge_two hn S hS x₀

end Geometry.Perimeter
