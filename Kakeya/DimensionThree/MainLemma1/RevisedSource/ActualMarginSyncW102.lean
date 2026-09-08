module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginNetW102

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The midpoint localization is retained from the same net witness as the
cover, separation, and carrier localization. -/
theorem exists_scaled_grid_net_with_midpoint_w102
    {rho alpha : NNReal} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ G : Finset (Tube (alpha * rho) E),
      (∀ {sigma : NNReal} (U : Tube sigma E),
        2 * (sigma : Real) ≤ (alpha * rho : Real) →
        U.midpoint ∈ Metric.closedBall (0 : E) 3 →
        ∃ W ∈ G, U.toConvexSpaceBody ≤ W.toConvexSpaceBody ∧
          ‖U.midpoint - W.midpoint‖ ≤ (alpha * rho : Real) / 32 ∧
          ‖U.direction - W.direction‖ ≤ (alpha * rho : Real) / 16) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ≠ b →
        (alpha * rho : Real) / 32 ≤ ‖a.x - b.x‖ + ‖a.y - b.y‖) ∧
      (∀ W ∈ G, W.carrier ⊆ Metric.closedBall (0 : E) 5) ∧
      (∀ W ∈ G, W.midpoint ∈ Metric.closedBall (0 : E) 3) := by
  have hprod : 0 < alpha * rho := mul_pos halpha hrho
  have hprod1 : (alpha * rho : Real) ≤ 1 := by
    exact_mod_cast (mul_le_one₀ halpha1 (by positivity) hrho1)
  obtain ⟨G, hcover, hsep, hball, hmid⟩ :=
    Tube.grid_net_tight (E := E) hprod hprod1
  exact ⟨G, hcover, hsep, hball, hmid⟩

end
end Kakeya.ml1Boot.TrialRestartW94
