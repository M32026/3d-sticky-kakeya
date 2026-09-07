import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseRectangleShortening
import MyLeanRepo.Kakeya.Cinematic.Section5.RectangleShortening

/-!
# Enlarge the common fine-rectangle scale constant

Increasing `C_R` shortens every horizontal interval while preserving the
distinguished midpoint, point membership, centrality, centers, fibers, and
tangency certificates.
-/

namespace Kakeya.Cinematic

lemma fine_assignment_enlarge_C_R
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta t Delta C_R₀ C_R : ℝ}
    (data : FineRectangleAssignmentData
      family E K delta t Delta C_R₀)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hDelta : 0 < Delta)
    (hC_R₀ : 0 < C_R₀)
    (hC_R : 0 < C_R)
    (hC_R_le : C_R₀ ≤ C_R) :
    ∃ data' : FineRectangleAssignmentData
        family E K delta t Delta C_R,
      data'.interval = data.interval ∧
      (∀ p : E, data'.center p = data.center p) ∧
      ∀ p : E, data'.fiber p = data.fiber p := by
  let exactScale : E → ℝ :=
    fun _ => C_R₀ * t * Delta / delta
  have hexact : ∀ p : E, 0 < exactScale p := by
    intro p
    dsimp only [exactScale]
    positivity
  have hcommon : 0 < C_R * t * Delta / delta := by
    positivity
  have hscale : ∀ p : E,
      exactScale p ≤ C_R * t * Delta / delta := by
    intro p
    dsimp only [exactScale]
    apply div_le_div_of_nonneg_right
    · gcongr
    · exact hdelta.le
  exact
    pointwise_rectangle_shortening rectangle_shortening
      (I := data.interval) data.intervalControlled
      data.point data.point_coe
      data.center data.center_mem
      data.fiber data.fiber_subset
      exactScale hdelta hcommon
      hexact hscale
      data.rectangle
      data.rectangle_function
      data.rectangle_midpoint
      data.rectangle_midpoint_central
      data.point_mem_rectangle
      data.rectangle_central
      data.fiber_tangent

end Kakeya.Cinematic
