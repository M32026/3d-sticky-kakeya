import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Endpoint balls inside a tube

At small radius, the two endpoint balls of a unit tube are disjoint and both
lie inside its carrier.  Their combined volume gives a concrete tube-volume
lower bound for later overlap comparisons.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The two radius-`rho` endpoint balls of a unit tube are disjoint when
`2 * rho < 1`, and their total volume is bounded by the tube volume.
-/
lemma tube_endpoint_balls_volume_lower
    {rho : ℝ} (hrho_small : 2 * rho < 1)
    (T : Kakeya.DeltaTube rho) :
    2 * volume (Metric.closedBall (0 : Point3) rho) ≤ T.volume := by
  let left : Set Point3 := Metric.closedBall T.base rho
  let right : Set Point3 :=
    Metric.closedBall (T.base + T.direction) rho
  have hleft_axis :
      T.base ∈ Kakeya.unitSegment T.base T.direction :=
    ⟨0, by norm_num, by simp⟩
  have hright_axis :
      T.base + T.direction ∈
        Kakeya.unitSegment T.base T.direction :=
    ⟨1, by norm_num, by simp⟩
  have hleft : left ⊆ T.carrier := by
    intro point hpoint
    exact Metric.mem_cthickening_of_dist_le
      point T.base rho _ hleft_axis
      (by simpa [left, Metric.mem_closedBall] using hpoint)
  have hright : right ⊆ T.carrier := by
    intro point hpoint
    exact Metric.mem_cthickening_of_dist_le
      point (T.base + T.direction) rho _ hright_axis
      (by simpa [right, Metric.mem_closedBall] using hpoint)
  have hcenters :
      dist T.base (T.base + T.direction) = 1 := by
    rw [dist_eq_norm]
    have hsub :
        T.base - (T.base + T.direction) = -T.direction := by
      abel
    rw [hsub, norm_neg, T.direction_unit]
  have hdisjoint : Disjoint left right := by
    apply Metric.closedBall_disjoint_closedBall
    rw [hcenters]
    linarith
  have hunion : left ∪ right ⊆ T.carrier :=
    Set.union_subset hleft hright
  have hmeasure :
      volume (left ∪ right) = volume left + volume right :=
    measure_union hdisjoint Metric.isClosed_closedBall.measurableSet
  have hball_eq :
      volume left = volume (Metric.closedBall (0 : Point3) rho) ∧
      volume right = volume (Metric.closedBall (0 : Point3) rho) := by
    constructor <;>
      rw [EuclideanSpace.volume_closedBall_fin_three,
        EuclideanSpace.volume_closedBall_fin_three]
  calc
    2 * volume (Metric.closedBall (0 : Point3) rho)
        = volume left + volume right := by
          rw [hball_eq.1, hball_eq.2]
          ring
    _ = volume (left ∪ right) := hmeasure.symm
    _ ≤ volume T.carrier := measure_mono hunion
    _ = T.volume := rfl

end Kakeya.Assouad
