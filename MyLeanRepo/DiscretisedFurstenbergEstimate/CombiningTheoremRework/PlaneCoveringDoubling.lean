module

/-
  Plane covering doubling lemma — isolated from NearbyDyadicTransfer.

  Provides `plane_covering_doubling`: covering number at scale r is bounded
  by 9 times the covering number at scale 2r, for EuclideanPlane.

  This is the only fact needed from Section 9 by the Theorem 6.1 path.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate

noncomputable section

namespace DiscretisedFurstenbergEstimate.PlaneCoveringDoubling

/-- Covering doubling for EuclideanPlane with constant 9. -/
lemma plane_covering_doubling {r : ℝ} (hr_pos : 0 < r)
    (A : Set EuclideanPlane) :
    (Metric.externalCoveringNumber r.toNNReal A : ENNReal) ≤
      (9 : ENNReal) * (Metric.externalCoveringNumber (2 * r).toNNReal A : ENNReal) := by
  have h := externalCoveringNumber_half_le_plane A (2 * r).toNNReal
  have h2 : (2 * r).toNNReal / 2 = r.toNNReal := by
    apply NNReal.coe_injective
    simp [NNReal.coe_div, hr_pos.le] <;> ring
  rw [h2] at h
  exact_mod_cast h

end DiscretisedFurstenbergEstimate.PlaneCoveringDoubling

end
