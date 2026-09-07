import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Ball-in-tube lower bound

For a point in a `rho`-tube, the intersection of that tube with the
radius-`rho` ball around the point contains a radius-`rho / 2` ball.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

lemma tube_ball_density_rho
    {rho : ℝ} (hrho : 0 < rho)
    (S : Kakeya.DeltaTube rho)
    {x : Point3} (hx : x ∈ S.carrier) :
    MeasureTheory.volume
        (S.carrier ∩ Metric.closedBall x rho) ≥
      ENNReal.ofReal (Real.pi * rho ^ 3 / 6) := by
  let seg := Kakeya.unitSegment S.base S.direction
  have hseg_compact : IsCompact seg := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  have hcarrier :
      S.carrier = ⋃ y ∈ seg, Metric.closedBall y rho :=
    hseg_compact.cthickening_eq_biUnion_closedBall (by linarith)
  have h_exists :
      ∃ y : Point3, y ∈ seg ∧
        x ∈ Metric.closedBall y rho := by
    rw [hcarrier] at hx
    simpa [Set.mem_iUnion] using hx
  rcases h_exists with ⟨y, hy, hxy⟩
  have hdist : dist x y ≤ rho := by
    simpa [Metric.mem_closedBall] using hxy
  let m : Point3 := (1 / 2 : ℝ) • (x + y)
  have h_eq_mx : m - x = (1 / 2 : ℝ) • (y - x) := by
    ext i
    simp [m]
    ring
  have h_eq_my : m - y = (1 / 2 : ℝ) • (x - y) := by
    ext i
    simp [m]
    ring
  have hnorm_half : ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) := by
    simp
  have hdist_mx :
      dist m x = (1 / 2 : ℝ) * dist x y := by
    calc
      dist m x = ‖m - x‖ := by rw [dist_eq_norm]
      _ = ‖(1 / 2 : ℝ) • (y - x)‖ := by rw [h_eq_mx]
      _ = ‖(1 / 2 : ℝ)‖ * ‖y - x‖ := by rw [norm_smul]
      _ = (1 / 2 : ℝ) * ‖y - x‖ := by rw [hnorm_half]
      _ = (1 / 2 : ℝ) * ‖x - y‖ := by
        rw [← neg_sub x y, norm_neg]
      _ = (1 / 2 : ℝ) * dist x y := by rw [← dist_eq_norm]
  have hdist_my :
      dist m y = (1 / 2 : ℝ) * dist x y := by
    calc
      dist m y = ‖m - y‖ := by rw [dist_eq_norm]
      _ = ‖(1 / 2 : ℝ) • (x - y)‖ := by rw [h_eq_my]
      _ = ‖(1 / 2 : ℝ)‖ * ‖x - y‖ := by rw [norm_smul]
      _ = (1 / 2 : ℝ) * ‖x - y‖ := by rw [hnorm_half]
      _ = (1 / 2 : ℝ) * dist x y := by rw [← dist_eq_norm]
  have hdist_mx_le : dist m x ≤ rho / 2 := by
    rw [hdist_mx]
    linarith
  have hdist_my_le : dist m y ≤ rho / 2 := by
    rw [hdist_my]
    linarith
  have h1 :
      Metric.closedBall m (rho / 2) ⊆
        Metric.closedBall x rho := by
    intro z hz
    have h2 : dist z m ≤ rho / 2 := by
      simpa [Metric.mem_closedBall] using hz
    have h3 : dist z x ≤ rho := by
      calc
        dist z x ≤ dist z m + dist m x := dist_triangle _ _ _
        _ ≤ rho / 2 + rho / 2 := by gcongr
        _ = rho := by ring
    simpa [Metric.mem_closedBall] using h3
  have h2 :
      Metric.closedBall m (rho / 2) ⊆
        Metric.closedBall y rho := by
    intro z hz
    have h3 : dist z m ≤ rho / 2 := by
      simpa [Metric.mem_closedBall] using hz
    have h4 : dist z y ≤ rho := by
      calc
        dist z y ≤ dist z m + dist m y := dist_triangle _ _ _
        _ ≤ rho / 2 + rho / 2 := by gcongr
        _ = rho := by ring
    simpa [Metric.mem_closedBall] using h4
  have h3 : Metric.closedBall y rho ⊆ S.carrier := by
    intro z hz
    have h5 : z ∈ ⋃ w ∈ seg, Metric.closedBall w rho := by
      simp only [Set.mem_iUnion]
      exact ⟨y, hy, hz⟩
    rw [hcarrier]
    exact h5
  have h4 :
      Metric.closedBall m (rho / 2) ⊆
        S.carrier ∩ Metric.closedBall x rho := by
    intro z hz
    exact ⟨h3 (h2 hz), h1 hz⟩
  have hrho2 : 0 ≤ rho / 2 := by linarith
  have hvol_formula :
      MeasureTheory.volume (Metric.closedBall m (rho / 2)) =
        (ENNReal.ofReal (rho / 2)) ^ 3 *
          ENNReal.ofReal (Real.pi * 4 / 3) := by
    rw [EuclideanSpace.volume_closedBall_fin_three]
  have hvol_pow :
      (ENNReal.ofReal (rho / 2)) ^ 3 =
        ENNReal.ofReal ((rho / 2) ^ 3) := by
    rw [← ENNReal.ofReal_pow hrho2]
  have hvol_mul :
      ENNReal.ofReal ((rho / 2) ^ 3) *
          ENNReal.ofReal (Real.pi * 4 / 3) =
        ENNReal.ofReal
          (((rho / 2) ^ 3) * (Real.pi * 4 / 3)) := by
    rw [← ENNReal.ofReal_mul] <;> positivity
  have hvol_arith :
      ((rho / 2) ^ 3) * (Real.pi * 4 / 3) =
        Real.pi * rho ^ 3 / 6 := by
    ring
  have hvol :
      MeasureTheory.volume (Metric.closedBall m (rho / 2)) =
        ENNReal.ofReal (Real.pi * rho ^ 3 / 6) := by
    rw [hvol_formula, hvol_pow, hvol_mul, hvol_arith]
  calc
    MeasureTheory.volume
        (S.carrier ∩ Metric.closedBall x rho) ≥
      MeasureTheory.volume (Metric.closedBall m (rho / 2)) :=
        measure_mono h4
    _ = ENNReal.ofReal (Real.pi * rho ^ 3 / 6) := hvol

end Kakeya.Assouad
