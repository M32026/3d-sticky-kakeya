import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Support lemmas for the geometric overlap argument

Contains the numerical inequality showing cylinder volume exceeds half tube
volume, and the lemma verifying the cylinder lies in both tube carriers.

Whiteprint node: `Kakeya/WZ1CoarseDirectionPacking/OverlapSupport`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/-- Numerical inequality: for `0 < rho ≤ 1/10000`, the cylinder volume
`(3/4 - rho/100 - (rho/100)^2) * π * (49/50)^2` strictly exceeds
`2 + 4*rho`, which is twice the upper bound `1 + 2*rho` for half a tube volume. -/
lemma cylinder_numerical_inequality {rho : ℝ} (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 10000) :
    (3 / 4 - rho / 100 - (rho / 100)^2) * Real.pi * (49 / 50 : ℝ)^2 > 2 + 4 * rho := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h_pos : 0 < 3 / 4 - rho / 100 - (rho / 100)^2 := by
    nlinarith [hrho_small]
  nlinarith [sq_nonneg (rho - 1 / 10000), sq_nonneg (rho / 100)]

/-- A cylinder of radius `49*rho/50` around a subsegment of T's axis, whose
axis points are within `rho/50` of some point on U's unit segment, is contained
in both tube carriers. -/
lemma cylinder_in_intersection {rho : ℝ} (hrho : 0 < rho)
    (T U : DeltaTube rho)
    (a b : ℝ) (hab : a ≤ b)
    (h_ab_in_Icc : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1)
    (h1 : ∀ s ∈ Set.Icc a b, ∃ (z : Point3),
      z ∈ Kakeya.unitSegment U.base U.direction ∧
      dist (T.base + s • T.direction) z ≤ rho / 50) :
    {x : Point3 | ∃ s ∈ Set.Icc a b, ∃ (e : Point3),
      inner ℝ e T.direction = 0 ∧ ‖e‖ ≤ 49 * rho / 50 ∧
      x = T.base + s • T.direction + e}
    ⊆ T.carrier ∩ U.carrier := by
  intro x hx
  rcases hx with ⟨s, hs, e, _he_perp, he_norm, rfl⟩
  have hs_in : s ∈ Set.Icc (0 : ℝ) 1 := h_ab_in_Icc hs
  let y : Point3 := T.base + s • T.direction
  have hy_in_T : y ∈ Kakeya.unitSegment T.base T.direction :=
    ⟨s, hs_in, rfl⟩
  have h_norm : ‖e‖ ≤ 49 * rho / 50 := he_norm
  have h_lt_rho : ‖e‖ ≤ rho := by linarith
  have h_dist_y : dist (y + e) y = ‖e‖ := by
    simp [dist_eq_norm]
    <;> abel
  have h_segment_compact : ∀ (base direction : Point3), IsCompact (Kakeya.unitSegment base direction) := by
    intro base direction
    exact isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  -- Inclusion in T.carrier
  have hT : y + e ∈ T.carrier := by
    have hcarrier : T.carrier = Metric.cthickening rho (Kakeya.unitSegment T.base T.direction) := by
      simp [DeltaTube.carrier]
    rw [hcarrier]
    have hcompact := h_segment_compact T.base T.direction
    rw [hcompact.cthickening_eq_biUnion_closedBall (by linarith)]
    exact Set.mem_iUnion₂.mpr ⟨y, hy_in_T, by
      simpa [Metric.mem_closedBall, h_dist_y] using h_lt_rho⟩
  -- Inclusion in U.carrier
  have hU : y + e ∈ U.carrier := by
    rcases h1 s hs with ⟨z, hz, hdist⟩
    have hcarrier : U.carrier = Metric.cthickening rho (Kakeya.unitSegment U.base U.direction) := by
      simp [DeltaTube.carrier]
    rw [hcarrier]
    have hcompact := h_segment_compact U.base U.direction
    rw [hcompact.cthickening_eq_biUnion_closedBall (by linarith)]
    have h : dist (y + e) z ≤ rho := by
      calc
        dist (y + e) z ≤ dist (y + e) y + dist y z := dist_triangle _ _ _
        _ = ‖e‖ + dist y z := by rw [h_dist_y] <;> ring
        _ ≤ 49 * rho / 50 + rho / 50 := by gcongr
        _ = rho := by ring
    exact Set.mem_iUnion₂.mpr ⟨z, hz, by simpa [Metric.mem_closedBall] using h⟩
  exact ⟨hT, hU⟩

end Kakeya.Assouad
