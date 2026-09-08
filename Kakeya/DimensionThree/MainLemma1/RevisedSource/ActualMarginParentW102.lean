module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualMarginSyncW102

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

/-- One synchronized parent choice: all geometric outputs refer to the same
small-net node, and its target-radius rescale inherits the child containment. -/
theorem exists_scaled_parent_step_w102
    {rho alpha sigma : NNReal} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hscale : 2 * (sigma : Real) ≤ (alpha * rho : Real))
    (U : Tube sigma E)
    (hUmid : U.midpoint ∈ Metric.closedBall (0 : E) 3) :
    ∃ (G : Finset (Tube (alpha * rho) E)) (W : Tube (alpha * rho) E),
      W ∈ G ∧ U.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody ∧
        ‖U.midpoint - W.midpoint‖ ≤ (alpha * rho : Real) / 32 ∧
        ‖U.direction - W.direction‖ ≤ (alpha * rho : Real) / 16 := by
  obtain ⟨G, hcover, _hsep, _hball, _hmid⟩ :=
    exists_scaled_grid_net_with_midpoint_w102 (E := E) hrho hrho1 halpha halpha1
  obtain ⟨W, hWG, hUW, hmid, hdir⟩ := hcover U hscale hUmid
  have hαrho : (alpha * rho : NNReal) ≤ rho := by
    exact mul_le_of_le_one_left rho.coe_nonneg halpha1
  have hWrescale : W.toConvexSpaceBody ≤ (W.rescale rho).toConvexSpaceBody := by
    simpa only [Tube.toConvexSpaceBody_rescale_self] using
      (Tube.rescale_le_rescale_of_radius_le W hαrho)
  refine ⟨G, W, hWG, hUW.trans hWrescale, hmid, hdir⟩

end
end Kakeya.ml1Boot.TrialRestartW94
