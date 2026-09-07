import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers
import Mathlib.Analysis.Convex.Measure

/-!
# Grid cube diameter and covering lemmas

Provides geometric lemmas about paper grid cubes used in the anisotropic
rescaling transfer for the large-slope proof.

## Main results

1. `dist_le_sqrt3_of_mem_wz1PaperGridCube`: any two points in the same
   `rho`-grid cube are at distance at most `rho * sqrt 3`.

2. `h_cover_of_balls`: if every source point has a closed ball of radius `r`
   contained in the carrier, and `rho * sqrt 3 ≤ r`, then every source point
   lies in a `rho`-grid cube fully contained in the carrier. This supplies
   the `h_cover` hypothesis needed by `denseCubicalizationInSet`.

## Whiteprint node

`Node6LargeSlope/SlopeConstruction/TransferCubical`
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/--
If two real numbers are both in the half-open interval `[z * s, (z+1) * s)`,
their absolute difference is strictly less than `s`.
-/
private lemma abs_sub_lt_s_of_same_floor_interval
    {s : ℝ} {z : ℤ} {x y : ℝ}
    (hx : (z : ℝ) * s ≤ x ∧ x < ((z : ℝ) + 1) * s)
    (hy : (z : ℝ) * s ≤ y ∧ y < ((z : ℝ) + 1) * s) :
    |x - y| < s := by
  have h1 : x - y < s := by linarith
  have h2 : -s < x - y := by linarith
  exact abs_lt.mpr ⟨h2, h1⟩

/--
Diameter bound for a paper grid cube: any two points in the same `rho`-grid
cube are at Euclidean distance at most `rho * Real.sqrt 3`.

Proof: each coordinate lies in an interval of length `rho`, so the squared
distance is at most `3 * rho^2`.
-/
lemma dist_le_sqrt3_of_mem_wz1PaperGridCube
    {rho : ℝ} (hrho : 0 < rho)
    {p q : Point3} {cell : ℤ × ℤ × ℤ}
    (hp : p ∈ wz1PaperGridCube rho cell)
    (hq : q ∈ wz1PaperGridCube rho cell) :
    dist p q ≤ rho * Real.sqrt 3 := by
  have hbox : wz1PaperGridCube rho cell =
      {x : Point3 |
        (cell.1 : ℝ) * rho ≤ x 0 ∧ x 0 < ((cell.1 : ℝ) + 1) * rho ∧
        (cell.2.1 : ℝ) * rho ≤ x 1 ∧ x 1 < ((cell.2.1 : ℝ) + 1) * rho ∧
        (cell.2.2 : ℝ) * rho ≤ x 2 ∧ x 2 < ((cell.2.2 : ℝ) + 1) * rho} :=
    wz1PaperGridCube_eq_Ico hrho cell
  rw [hbox] at hp hq
  have hp0 : (cell.1 : ℝ) * rho ≤ p 0 ∧ p 0 < ((cell.1 : ℝ) + 1) * rho :=
    ⟨hp.1, hp.2.1⟩
  have hp1 : (cell.2.1 : ℝ) * rho ≤ p 1 ∧ p 1 < ((cell.2.1 : ℝ) + 1) * rho :=
    ⟨hp.2.2.1, hp.2.2.2.1⟩
  have hp2 : (cell.2.2 : ℝ) * rho ≤ p 2 ∧ p 2 < ((cell.2.2 : ℝ) + 1) * rho :=
    ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
  have hq0 : (cell.1 : ℝ) * rho ≤ q 0 ∧ q 0 < ((cell.1 : ℝ) + 1) * rho :=
    ⟨hq.1, hq.2.1⟩
  have hq1 : (cell.2.1 : ℝ) * rho ≤ q 1 ∧ q 1 < ((cell.2.1 : ℝ) + 1) * rho :=
    ⟨hq.2.2.1, hq.2.2.2.1⟩
  have hq2 : (cell.2.2 : ℝ) * rho ≤ q 2 ∧ q 2 < ((cell.2.2 : ℝ) + 1) * rho :=
    ⟨hq.2.2.2.2.1, hq.2.2.2.2.2⟩
  have hc0 : |p 0 - q 0| < rho := abs_sub_lt_s_of_same_floor_interval hp0 hq0
  have hc1 : |p 1 - q 1| < rho := abs_sub_lt_s_of_same_floor_interval hp1 hq1
  have hc2 : |p 2 - q 2| < rho := abs_sub_lt_s_of_same_floor_interval hp2 hq2
  have h_coords : ∀ (i : Fin 3), |p i - q i| ≤ rho := by
    intro i
    fin_cases i
    · exact hc0.le
    · exact hc1.le
    · exact hc2.le
  have h_sum : ∑ i : Fin 3, (p i - q i) ^ 2 ≤ 3 * rho ^ 2 := by
    have h5 : ∑ i : Fin 3, (p i - q i) ^ 2 ≤ ∑ i : Fin 3, rho ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h6 : |p i - q i| ≤ rho := h_coords i
      calc
        (p i - q i) ^ 2 = |p i - q i| ^ 2 := by rw [sq_abs]
        _ ≤ rho ^ 2 := by gcongr
    calc
      _ ≤ ∑ _i : Fin 3, rho ^ 2 := h5
      _ = 3 * rho ^ 2 := by simp [Finset.sum_const]
  have h_norm2 : ‖p - q‖ ^ 2 = ∑ i : Fin 3, (p i - q i) ^ 2 := by
    have h7 : ‖p - q‖ = Real.sqrt (∑ i : Fin 3, |(p - q) i| ^ 2) :=
      PiLp.norm_eq_of_L2 (p - q)
    rw [h7]
    have h8 : 0 ≤ ∑ i : Fin 3, |(p - q) i| ^ 2 := by positivity
    rw [Real.sq_sqrt h8]
    apply Finset.sum_congr rfl
    intro i _
    have h9 : (p - q) i = p i - q i := by rfl
    rw [h9, sq_abs]
  have h_dist : dist p q = ‖p - q‖ := dist_eq_norm p q
  have h_dist2 : dist p q ^ 2 ≤ 3 * rho ^ 2 := by
    rw [h_dist, h_norm2]
    exact h_sum
  have h_goal : dist p q ≤ rho * Real.sqrt 3 := by
    by_contra h
    have h' : rho * Real.sqrt 3 < dist p q := by linarith
    have h15 : (rho * Real.sqrt 3) ^ 2 < (dist p q) ^ 2 := by gcongr
    have h16 : (rho * Real.sqrt 3) ^ 2 = 3 * rho ^ 2 := by
      calc
        (rho * Real.sqrt 3) ^ 2
          = rho ^ 2 * (Real.sqrt 3) ^ 2 := by ring
        _ = rho ^ 2 * 3 := by rw [Real.sq_sqrt (by norm_num)]
        _ = 3 * rho ^ 2 := by ring
    rw [h16] at h15
    linarith [h_dist2]
  exact h_goal

/--
Ball-to-cube covering lemma.

If every source point has a closed ball of radius `r` fully contained in the
carrier, and `rho * Real.sqrt 3 ≤ r`, then every source point lies in a
`rho`-grid cube fully contained in the carrier.

This provides the `h_cover` hypothesis for `denseCubicalizationInSet`: the
cube containing each source point is selected, and its diameter `rho * sqrt 3`
fits inside the ball of radius `r` around the point.
-/
lemma h_cover_of_balls
    {rho r : ℝ} (hrho : 0 < rho)
    (h : rho * Real.sqrt 3 ≤ r)
    {carrier source : Set Point3}
    (hballs : ∀ p ∈ source, Metric.closedBall p r ⊆ carrier) :
    ∀ p ∈ source,
      ∃ (cell : ℤ × ℤ × ℤ),
        p ∈ wz1PaperGridCube rho cell ∧
        wz1PaperGridCube rho cell ⊆ carrier := by
  intro p hp
  let cell := wz1PaperGridIndex rho p
  have h1 : p ∈ wz1PaperGridCube rho cell :=
    (mem_wz1PaperGridCube rho cell p).mpr rfl
  have h2 : ∀ q ∈ wz1PaperGridCube rho cell, dist p q ≤ rho * Real.sqrt 3 := by
    intro q hq
    exact dist_le_sqrt3_of_mem_wz1PaperGridCube hrho h1 hq
  have h3 : wz1PaperGridCube rho cell ⊆ Metric.closedBall p (rho * Real.sqrt 3) := by
    intro q hq
    exact Metric.mem_closedBall.mpr (by rw [dist_comm]; exact h2 q hq)
  have h4 : Metric.closedBall p (rho * Real.sqrt 3) ⊆ Metric.closedBall p r := by
    intro x hx
    exact Metric.mem_closedBall.mpr
      ((Metric.mem_closedBall.mp hx).trans h)
  exact ⟨cell, h1, h3.trans (h4.trans (hballs p hp))⟩

end Kakeya.Assouad

end
