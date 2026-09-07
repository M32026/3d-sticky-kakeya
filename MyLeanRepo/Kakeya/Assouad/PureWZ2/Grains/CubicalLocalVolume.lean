import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Positive local volume from cubical shading

If a point `q` is in the union of a cubical tube shading, then the intersection
of the shading union with `ball(q, 4τ)` has positive volume, where `τ = L * √3`.

This follows because the cubical property guarantees the entire grid cube at `q`
is contained in the carrier, and the grid cube has diameter `≤ τ` and volume `L³`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Metric ENNReal

attribute [local instance] Classical.propDecidable

/-- If `⌊x/L⌋ = ⌊y/L⌋`, then `|x - y| < L`. -/
private lemma floor_eq_abs_sub_lt {L : ℝ} (hL_pos : 0 < L) {x y : ℝ}
    (h : ⌊x / L⌋ = ⌊y / L⌋) : |x - y| < L := by
  have h3 : |x / L - y / L| < 1 := Int.abs_sub_lt_one_of_floor_eq_floor h
  have h4 : |(x - y) / L| < 1 := by
    have h5 : (x - y) / L = x / L - y / L := by ring
    rw [h5]; exact h3
  have h6 : |x - y| / L < 1 := by
    have h7 : |(x - y) / L| = |x - y| / L := by
      rw [abs_div] <;> simp [abs_of_pos hL_pos]
    rw [h7] at h4; exact h4
  calc |x - y|
    = (|x - y| / L) * L := by field_simp [hL_pos.ne'] <;> ring
  _ < 1 * L := by gcongr
  _ = L := by ring

/-- Distance between two points in the same grid cube at scale `L` is `< √3 * L`. -/
lemma grid_cube_dist_lt_sqrt3 {L : ℝ} (hL_pos : 0 < L) {p q : Point3}
    (h : wz1PaperGridIndex L p = wz1PaperGridIndex L q) :
    dist p q < Real.sqrt 3 * L := by
  have h0 : ⌊(p 0) / L⌋ = ⌊(q 0) / L⌋ := by
    have h' : (wz1PaperGridIndex L p).1 = (wz1PaperGridIndex L q).1 := by rw [h]
    simpa [wz1PaperGridIndex, gridIndex] using h'
  have h1 : ⌊(p 1) / L⌋ = ⌊(q 1) / L⌋ := by
    have h' : (wz1PaperGridIndex L p).2.1 = (wz1PaperGridIndex L q).2.1 := by rw [h]
    simpa [wz1PaperGridIndex, gridIndex] using h'
  have h2 : ⌊(p 2) / L⌋ = ⌊(q 2) / L⌋ := by
    have h' : (wz1PaperGridIndex L p).2.2 = (wz1PaperGridIndex L q).2.2 := by rw [h]
    simpa [wz1PaperGridIndex, gridIndex] using h'
  have b0 : |(p 0) - (q 0)| < L := floor_eq_abs_sub_lt hL_pos h0
  have b1 : |(p 1) - (q 1)| < L := floor_eq_abs_sub_lt hL_pos h1
  have b2 : |(p 2) - (q 2)| < L := floor_eq_abs_sub_lt hL_pos h2
  have hsq0 : ((p 0) - (q 0)) ^ 2 < L ^ 2 := by
    have h1 : -L < (p 0) - (q 0) := (abs_lt.mp b0).1
    have h2 : (p 0) - (q 0) < L := (abs_lt.mp b0).2
    nlinarith
  have hsq1 : ((p 1) - (q 1)) ^ 2 < L ^ 2 := by
    have h1 : -L < (p 1) - (q 1) := (abs_lt.mp b1).1
    have h2 : (p 1) - (q 1) < L := (abs_lt.mp b1).2
    nlinarith
  have hsq2 : ((p 2) - (q 2)) ^ 2 < L ^ 2 := by
    have h1 : -L < (p 2) - (q 2) := (abs_lt.mp b2).1
    have h2 : (p 2) - (q 2) < L := (abs_lt.mp b2).2
    nlinarith
  have hsum3 : ((p 0) - (q 0)) ^ 2 + ((p 1) - (q 1)) ^ 2 + ((p 2) - (q 2)) ^ 2 < 3 * L ^ 2 := by
    nlinarith
  have h_sum_eq : ∑ i : Fin 3, ‖(p - q) i‖ ^ 2 = ∑ i : Fin 3, ((p - q) i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    have h1 : ‖(p - q) i‖ = |(p - q) i| := by simp [Real.norm_eq_abs]
    rw [h1, sq_abs]
  have h_pos : 0 ≤ ∑ i : Fin 3, ((p - q) i)^2 := by positivity
  have h_norm2 : ‖p - q‖ ^ 2 = ∑ i : Fin 3, ((p - q) i)^2 := by
    have h : ‖p - q‖ = Real.sqrt (∑ i : Fin 3, ‖(p - q) i‖ ^ 2) := by
      rw [PiLp.norm_eq_of_L2] <;> rfl
    rw [h, h_sum_eq, Real.sq_sqrt h_pos]
  have h_coords : ∑ i : Fin 3, ((p - q) i)^2 =
      ((p 0) - (q 0)) ^ 2 + ((p 1) - (q 1)) ^ 2 + ((p 2) - (q 2)) ^ 2 := by
    simp [Fin.sum_univ_succ] <;> ring
  have hdist_sq : dist p q ^ 2 < 3 * L ^ 2 := by
    rw [dist_eq_norm, h_norm2, h_coords]
    exact hsum3
  have h7 : 0 ≤ ‖p - q‖ := by positivity
  have h8 : 0 ≤ Real.sqrt 3 * L := by positivity
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

/-- If `q` is in a cubical shading union, then `shading.union ∩ ball(q, 4τ)` has positive volume. -/
lemma cubical_shading_local_positive_volume
    {L : ℝ} {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (hcubical : WZ1PaperIsCubicalShading coarseShading)
    (hL_pos : 0 < L)
    (tau : ℝ)
    (htau_def : tau = L * Real.sqrt 3)
    (htau_pos : 0 < tau)
    (q : Point3)
    (hq : q ∈ coarseShading.union) :
    0 < volume (coarseShading.union ∩ Metric.closedBall q (4 * tau)) := by
  rcases hq with ⟨j, hj⟩
  let cell := wz1PaperGridIndex L q
  let cube := wz1PaperGridCube L cell
  have hcube_carrier : cube ⊆ coarseShading.carrier j :=
    hcubical j q hj
  have hcube_ball : cube ⊆ Metric.closedBall q tau := by
    intro p hp
    have hsame : wz1PaperGridIndex L p = cell := by
      simpa [cube, mem_wz1PaperGridCube] using hp
    have hdist : dist p q < Real.sqrt 3 * L := grid_cube_dist_lt_sqrt3 hL_pos hsame
    have htau_eq : tau = Real.sqrt 3 * L := by rw [htau_def] <;> ring
    rw [htau_eq]; exact hdist.le
  let S := coarseShading.union ∩ Metric.closedBall q (4 * tau)
  have hcube_S : cube ⊆ S := by
    intro p hp
    have h1 : p ∈ coarseShading.union := ⟨j, hcube_carrier hp⟩
    have h2 : dist p q ≤ tau := hcube_ball hp
    have h3 : dist p q ≤ 4 * tau := by linarith [htau_pos]
    exact ⟨h1, h3⟩
  have hvol : volume cube = ENNReal.ofReal (L ^ 3) :=
    wz1PaperGridCube_volume_any hL_pos cell
  have hpos_cube : 0 < volume cube := by
    rw [hvol]
    have h : 0 < L ^ 3 := by positivity
    simpa [ENNReal.ofReal_pos] using h
  have hle : volume cube ≤ volume S := measure_mono hcube_S
  exact lt_of_lt_of_le hpos_cube hle

/-- Upper bound on volume of a closed ball in `Point3`.

Uses the exact Euclidean ball volume formula `(4/3) * π * r^3` and bounds
the constant by `8`, giving `volume ≤ 8 * r^3 = (2*r)^3`. -/
lemma volume_closedBall_point3_le {q : Point3} {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall q r) ≤ ENNReal.ofReal ((2 * r) ^ 3) := by
  have h_card : Fintype.card (Fin 3) = 3 := by decide
  have h_arg : (3 / 2 + 1 : ℝ) = (5 / 2 : ℝ) := by norm_num
  have h_exact : volume (Metric.closedBall q r) =
      ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.sqrt Real.pi ^ 3 / Real.Gamma (5 / 2 : ℝ)) := by
    have h := EuclideanSpace.volume_closedBall (Fin 3) q r
    rw [h_card] at h
    simpa [h_arg, show (↑(Fintype.card (Fin 3)) / 2 + 1 : ℝ) = (5 / 2 : ℝ) by norm_num] using h
  have h_gamma_raw : Real.Gamma (2 + 1 / 2 : ℝ) = (3 : ℝ) * Real.sqrt Real.pi / 4 := by
    have h := Real.Gamma_nat_add_half 2
    simpa [Nat.doubleFactorial, show (2 ^ 2 : ℝ) = 4 by norm_num] using h
  have h_arg_eq : (2 + 1 / 2 : ℝ) = (5 / 2 : ℝ) := by norm_num
  have h1 : Real.Gamma (5 / 2 : ℝ) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    have h : Real.Gamma (2 + 1 / 2 : ℝ) = Real.Gamma (5 / 2 : ℝ) := by rw [h_arg_eq]
    rw [h] at h_gamma_raw
    have h_eq2 : (3 : ℝ) * Real.sqrt Real.pi / 4 = (3 / 4 : ℝ) * Real.sqrt Real.pi := by ring
    rw [h_eq2] at h_gamma_raw
    exact h_gamma_raw
  have h2 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h3 : Real.sqrt Real.pi ^ 3 / Real.Gamma (5 / 2 : ℝ) = (4 / 3 : ℝ) * Real.pi := by
    rw [h1]
    have h4 : Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi) = (4 / 3 : ℝ) * Real.pi := by
      calc
        Real.sqrt Real.pi ^ 3 / (3 / 4 * Real.sqrt Real.pi)
          = (Real.sqrt Real.pi ^ 2 * Real.sqrt Real.pi) / (3 / 4 * Real.sqrt Real.pi) := by ring
        _ = Real.sqrt Real.pi ^ 2 / (3 / 4 : ℝ) := by
          field_simp [h2.ne'] <;> ring
        _ = Real.pi / (3 / 4 : ℝ) := by
          have h5 : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt (by linarith [Real.pi_pos])
          rw [h5]
        _ = (4 / 3 : ℝ) * Real.pi := by ring
    exact h4
  have h_const : (4 / 3 : ℝ) * Real.pi ≤ 8 := by
    have h4 : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith
  have h5 : 0 ≤ (4 / 3 : ℝ) * Real.pi := by positivity
  have h_ofReal_pow : ENNReal.ofReal r ^ 3 = ENNReal.ofReal (r ^ 3) := by
    rw [ENNReal.ofReal_pow] <;> linarith
  rw [h_exact, h3, h_ofReal_pow]
  have h6 : ENNReal.ofReal (r ^ 3) * ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi) ≤
      ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (8 : ℝ) := by
    gcongr
    <;> exact h_const
  have h7 : ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (8 : ℝ) = ENNReal.ofReal ((2 * r) ^ 3) := by
    have h9 : 0 ≤ r ^ 3 := by positivity
    have h10 : ENNReal.ofReal (r ^ 3) * ENNReal.ofReal (8 : ℝ) = ENNReal.ofReal (r ^ 3 * 8) := by
      rw [← ENNReal.ofReal_mul h9] <;> rfl
    have h11 : r ^ 3 * 8 = (2 * r) ^ 3 := by ring
    rw [h10, h11]
  exact h6.trans (le_of_eq h7)

/-- Local volume upper bound for a set contained in `closedBall(q, 4τ)`.

Gives `(volume S).toReal ≤ 512 * τ^3`. -/
lemma local_volume_upper {tau : ℝ} (htau_pos : 0 < tau)
    (q : Point3) (S : Set Point3)
    (hS_sub : S ⊆ Metric.closedBall q (4 * tau)) :
    (volume S).toReal ≤ 512 * tau^3 := by
  have h1 : volume S ≤ volume (Metric.closedBall q (4 * tau)) := measure_mono hS_sub
  have h2 : volume (Metric.closedBall q (4 * tau)) ≤ ENNReal.ofReal ((2 * (4 * tau)) ^ 3) :=
    volume_closedBall_point3_le (by linarith [htau_pos])
  have h4 : (2 * (4 * tau)) ^ 3 = 512 * tau^3 := by ring
  rw [h4] at h2
  have h3 : volume S ≤ ENNReal.ofReal (512 * tau^3) := h1.trans h2
  have h_rhs_ne_top : ENNReal.ofReal (512 * tau^3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h4 : (volume S).toReal ≤ (ENNReal.ofReal (512 * tau^3)).toReal :=
    ENNReal.toReal_mono h_rhs_ne_top h3
  have h5 : (ENNReal.ofReal (512 * tau^3)).toReal = 512 * tau^3 := by
    rw [ENNReal.toReal_ofReal (by positivity)]
  rw [h5] at h4
  exact h4

end Kakeya.Assouad.PureWZ2

end
