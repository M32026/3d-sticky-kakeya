import MyLeanRepo.Kakeya.Assouad.WZ1.RobustCloseDirectionCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# CWA-based close direction count for paper tube shadings

Adapts the WZ1 robust close direction count (`wz1_robust_close_direction_count`)
to paper tube carriers (6δ-thick full lines cropped to `axisBox 2 2 2`).

## Key difference from WZ1

WZ1 tubes are δ-thick unit segments, so the parameter along the line is bounded
by 1. Paper tubes are 6L-thick full lines cropped to [-1,1]³, so the parameter
along the line is bounded by `2√3 + 12L` (the diameter of the box plus twice
the thickness). This gives a larger constant in the volume bound but the same
quadratic dependence on κ.

## Result

At threshold κ ≥ L, the close direction count is bounded by
`C * 10000 * κ² * coarse.enncard`, where `C` is the Convex-Wolff constant.

For small ε₃, choosing κ = L^ε₃ and C = L^(-loss) with loss < 2ε₃ gives
a bound that tends to zero as L → 0, making it feasible for the transverse
pair selection.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 500000

/-- The perpendicular projection `z ↦ z - inner(z, u)•u` satisfies linearity
and the difference formula needed for close-direction counting. Extracted as a
separate lemma to stay within heartbeat limits. -/
lemma perp_projection_radial_diff (dir_i : Point3) (x p r_x r_p dir_j : Point3) (t : ℝ)
    (h_diff : x - p = (x - r_x) + t • dir_j + (r_p - p)) :
    (x - p) - inner ℝ (x - p) dir_i • dir_i =
    ((x - r_x) - inner ℝ (x - r_x) dir_i • dir_i) +
    t • (dir_j - inner ℝ dir_j dir_i • dir_i) +
    ((r_p - p) - inner ℝ (r_p - p) dir_i • dir_i) := by
  have h1 : inner ℝ (x - p) dir_i = inner ℝ (x - r_x) dir_i + t * inner ℝ dir_j dir_i + inner ℝ (r_p - p) dir_i := by
    rw [h_diff]
    simp [inner_add_left, inner_smul_left] <;> ring
  ext k
  have h2 : (x - p) k = (x - r_x) k + t * dir_j k + (r_p - p) k := by
    rw [h_diff]
    simp [Pi.add_apply, Pi.smul_apply] <;> ring
  simp [h1, h2, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] <;> ring

/-- CWA-based close direction count bound for paper tube shadings.

All paper tubes whose directions are within κ of a given direction and whose
carriers contain p are contained in an oriented box of volume `10000 * κ²`.
The Convex-Wolff bound then limits their number. -/
lemma paper_cwa_close_direction_count
    {L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    {C : ENNReal}
    (hCWA : WZ2PaperConvexWolffBound coarse C)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 10000)
    (kappa : ℝ)
    (hkappa_pos : 0 < kappa)
    (hkappa_le_one : kappa ≤ 1)
    (hkappa_ge_L : L ≤ kappa)
    (p : Point3)
    (i : Fin coarse.card)
    (hp : p ∈ coarseShading.carrier i) :
    (paperCloseDirectionCount coarseShading p i kappa : ENNReal) ≤
      C * ENNReal.ofReal (10000 * kappa^2) * coarse.enncard := by
  classical
  let dir_i : Point3 := (coarse.tube i).direction
  have hdir_i_unit : ‖dir_i‖ = 1 := (coarse.tube i).direction_unit
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he0_std_unit : ‖e0_std‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (dir_i - e0_std))ᗮ
  have hA_dir_i : A dir_i = e0_std :=
    Submodule.reflection_sub (hdir_i_unit.trans he0_std_unit.symm)
  have hA_norm : ∀ (x : Point3), ‖A x‖ = ‖x‖ := A.norm_map
  have hcoord0 : ∀ (z : Point3), (A z) 0 = inner ℝ z dir_i := by
    intro z
    have h : (A z) 0 = inner ℝ (A z) e0_std := by
      have h2 : inner ℝ (A z) e0_std = (1 : ℝ) * (A z) 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e0_std = inner ℝ z (A.symm e0_std) := by
      have h4 := A.inner_map_map z (A.symm e0_std)
      have h5 : A (A.symm e0_std) = e0_std := A.apply_symm_apply e0_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e0_std = dir_i := by
      have h7 : A (A.symm e0_std) = A dir_i := by
        rw [A.apply_symm_apply, hA_dir_i]
      exact A.injective h7
    rw [h6]
  have hcoord_perp : ∀ (z : Point3),
      ‖z - inner ℝ z dir_i • dir_i‖ ^ 2 = |(A z) 1| ^ 2 + |(A z) 2| ^ 2 := by
    intro z
    let r := z - inner ℝ z dir_i • dir_i
    have hAr : A r = A z - inner ℝ z dir_i • e0_std := by
      have h1 : A r = A z - A (inner ℝ z dir_i • dir_i) := by
        rw [show r = z - inner ℝ z dir_i • dir_i from rfl, A.map_sub]
      rw [h1, A.map_smul, hA_dir_i] <;> rfl
    have hAr0 : (A r) 0 = 0 := by
      rw [hAr]
      have h : (A z - inner ℝ z dir_i • e0_std) 0 = (A z) 0 - inner ℝ z dir_i := by
        simp [e0_std] <;> ring
      rw [h, hcoord0] <;> ring
    have hAr1 : (A r) 1 = (A z) 1 := by
      rw [hAr]; simp [e0_std] <;> ring
    have hAr2 : (A r) 2 = (A z) 2 := by
      rw [hAr]; simp [e0_std] <;> ring
    have h_norm : ‖r‖ ^ 2 = ‖A r‖ ^ 2 := by rw [hA_norm r]
    have h_expand : ‖A r‖ ^ 2 = (A r) 0 ^ 2 + (A r) 1 ^ 2 + (A r) 2 ^ 2 :=
      point3_norm_sq (A r)
    have h_abs : ∀ (x : ℝ), |x| ^ 2 = x ^ 2 := by intro x; simp [abs_pow]
    rw [h_norm, h_expand, hAr0, hAr1, hAr2, h_abs ((A z) 1), h_abs ((A z) 2)] <;> ring
  let a0 : ℝ := 9 / 2
  let a1 : ℝ := 16 * kappa
  let a2 : ℝ := 16 * kappa
  let W : Set Point3 := {x |
    |(A (x - p)) 0| ≤ a0 ∧ |(A (x - p)) 1| ≤ a1 ∧ |(A (x - p)) 2| ≤ a2}
  have hW_convex : Convex ℝ W := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb hab
    have h_alg : a • x + b • y - p = a • (x - p) + b • (y - p) := by
      have h : a • x + b • y - p = a • x + b • y - (a + b) • p := by
        rw [hab] <;> simp
      rw [h]
      have h2 : (a + b) • p = a • p + b • p := add_smul a b p
      rw [h2]
      have h3 : a • x + b • y - (a • p + b • p) = a • (x - p) + b • (y - p) := by
        have h4 : a • x + b • y - (a • p + b • p) = (a • x - a • p) + (b • y - b • p) := by abel
        rw [h4]
        have h5 : a • x - a • p = a • (x - p) := by rw [← smul_sub]
        have h6 : b • y - b • p = b • (y - p) := by rw [← smul_sub]
        rw [h5, h6]
      exact h3
    have h_eq : A (a • x + b • y - p) = a • A (x - p) + b • A (y - p) := by
      rw [h_alg, A.map_add, A.map_smul, A.map_smul]
    have h_eval0 : (A (a • x + b • y - p)) 0 = a * (A (x - p)) 0 + b * (A (y - p)) 0 := by
      rw [h_eq] <;> rfl
    have h_eval1 : (A (a • x + b • y - p)) 1 = a * (A (x - p)) 1 + b * (A (y - p)) 1 := by
      rw [h_eq] <;> rfl
    have h_eval2 : (A (a • x + b • y - p)) 2 = a * (A (x - p)) 2 + b * (A (y - p)) 2 := by
      rw [h_eq] <;> rfl
    have h_abs : ∀ (u v : ℝ), |a * u + b * v| ≤ a * |u| + b * |v| := by
      intro u v
      have h1 : |a * u + b * v| ≤ |a * u| + |b * v| := abs_add_le _ _
      have ha' : |a * u| = a * |u| := by
        rw [abs_mul, abs_of_pos ha]
      have hb' : |b * v| = b * |v| := by
        rw [abs_mul, abs_of_pos hb]
      rw [ha', hb'] at h1
      exact h1
    have hx0 : |(A (x - p)) 0| ≤ a0 := hx.1
    have hy0 : |(A (y - p)) 0| ≤ a0 := hy.1
    have hx1 : |(A (x - p)) 1| ≤ a1 := hx.2.1
    have hy1 : |(A (y - p)) 1| ≤ a1 := hy.2.1
    have hx2 : |(A (x - p)) 2| ≤ a2 := hx.2.2
    have hy2 : |(A (y - p)) 2| ≤ a2 := hy.2.2
    have h_sum0 : a * a0 + b * a0 = a0 := by
      have h : a * a0 + b * a0 = (a + b) * a0 := by ring
      rw [h, hab] <;> ring
    have h_sum1 : a * a1 + b * a1 = a1 := by
      have h : a * a1 + b * a1 = (a + b) * a1 := by ring
      rw [h, hab] <;> ring
    have h_sum2 : a * a2 + b * a2 = a2 := by
      have h : a * a2 + b * a2 = (a + b) * a2 := by ring
      rw [h, hab] <;> ring
    have h1 : |a * (A (x - p)) 0 + b * (A (y - p)) 0| ≤ a0 := by
      calc
        |a * (A (x - p)) 0 + b * (A (y - p)) 0|
          ≤ a * |(A (x - p)) 0| + b * |(A (y - p)) 0| := h_abs _ _
        _ ≤ a * a0 + b * a0 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hx0 ha.le) (mul_le_mul_of_nonneg_left hy0 hb.le)
        _ = a0 := h_sum0
    have h2 : |a * (A (x - p)) 1 + b * (A (y - p)) 1| ≤ a1 := by
      calc
        |a * (A (x - p)) 1 + b * (A (y - p)) 1|
          ≤ a * |(A (x - p)) 1| + b * |(A (y - p)) 1| := h_abs _ _
        _ ≤ a * a1 + b * a1 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hx1 ha.le) (mul_le_mul_of_nonneg_left hy1 hb.le)
        _ = a1 := h_sum1
    have h3 : |a * (A (x - p)) 2 + b * (A (y - p)) 2| ≤ a2 := by
      calc
        |a * (A (x - p)) 2 + b * (A (y - p)) 2|
          ≤ a * |(A (x - p)) 2| + b * |(A (y - p)) 2| := h_abs _ _
        _ ≤ a * a2 + b * a2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hx2 ha.le) (mul_le_mul_of_nonneg_left hy2 hb.le)
        _ = a2 := h_sum2
    exact ⟨by rw [h_eval0] <;> exact h1, by rw [h_eval1] <;> exact h2,
      by rw [h_eval2] <;> exact h3⟩
  have h_volume : volume W ≤ ENNReal.ofReal (10000 * kappa^2) := by
    have hW_eq : W = {x |
        |(A (x - p)) 0| ≤ (2 * a0) / 2 ∧
        |(A (x - p)) 1| ≤ (2 * a1) / 2 ∧
        |(A (x - p)) 2| ≤ (2 * a2) / 2} := by
      ext x; simp [W, a0, a1, a2] <;> ring_nf <;> rfl
    have h_main : volume W ≤ ENNReal.ofReal ((2 * a0) * (2 * a1) * (2 * a2)) := by
      rw [hW_eq]
      exact oriented_box_volume_bound A p (2 * a0) (2 * a1) (2 * a2)
        (by positivity) (by positivity) (by positivity)
    have h_mul : (2 * a0) * (2 * a1) * (2 * a2) ≤ 10000 * kappa^2 := by
      simp [a0, a1, a2] <;> nlinarith
    have h_main' : volume W ≤ ENNReal.ofReal (10000 * kappa^2) := by
      calc
        volume W ≤ ENNReal.ofReal ((2 * a0) * (2 * a1) * (2 * a2)) := h_main
        _ ≤ ENNReal.ofReal (10000 * kappa^2) := ENNReal.ofReal_le_ofReal h_mul
    exact h_main'
  have h_containment : ∀ (j : Fin coarse.card),
      p ∈ coarseShading.carrier j →
      ‖wz1Cross dir_i (coarse.tube j).direction‖ < kappa →
      wz1PaperTubeCarrier (coarse.tube j) ⊆ W := by
    intro j hj_p hj_cross x hx
    set dir_j : Point3 := (coarse.tube j).direction with hdir_j_def
    have hdir_j_unit : ‖dir_j‖ = 1 := (coarse.tube j).direction_unit
    have hx_paper : x ∈ wz1PaperTubeCarrier (coarse.tube j) := hx
    have hx_thick : x ∈ Metric.cthickening (6 * L) (tubeAxisLine (coarse.tube j)) :=
      hx_paper.1
    have hx_box : x ∈ Kakeya.Streamlined.axisBox 2 2 2 := hx_paper.2
    have hp_paper : p ∈ wz1PaperTubeCarrier (coarse.tube j) :=
      coarseShading.subset_body j hj_p
    have hp_thick : p ∈ Metric.cthickening (6 * L) (tubeAxisLine (coarse.tube j)) :=
      hp_paper.1
    have hp_box : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := hp_paper.2
    have h_line_closed : IsClosed (tubeAxisLine (coarse.tube j)) :=
      isClosed_tubeAxisLine (coarse.tube j)
    have hx_thick' : ∃ (r_x : Point3), r_x ∈ tubeAxisLine (coarse.tube j) ∧ dist x r_x ≤ 6 * L :=
      exists_dist_le_of_mem_cthickening_closed h_line_closed (by positivity) hx_thick
    have hp_thick' : ∃ (r_p : Point3), r_p ∈ tubeAxisLine (coarse.tube j) ∧ dist p r_p ≤ 6 * L :=
      exists_dist_le_of_mem_cthickening_closed h_line_closed (by positivity) hp_thick
    rcases hx_thick' with ⟨r_x, hr_x_line, hr_x_dist⟩
    rcases hp_thick' with ⟨r_p, hr_p_line, hr_p_dist⟩
    have hr_x_norm : ‖x - r_x‖ ≤ 6 * L := by exact_mod_cast hr_x_dist
    have hr_p_norm : ‖r_p - p‖ ≤ 6 * L := by
      have h : dist p r_p = ‖p - r_p‖ := dist_eq_norm p r_p
      rw [h] at hr_p_dist
      have h2 : ‖p - r_p‖ = ‖r_p - p‖ := by rw [norm_sub_rev]
      rw [h2] at hr_p_dist
      exact hr_p_dist
    have h_line_diff : ∃ (t : ℝ), r_x - r_p = t • dir_j := by
      rcases hr_x_line with ⟨t_x, ht_x⟩
      rcases hr_p_line with ⟨t_p, ht_p⟩
      refine ⟨t_x - t_p, ?_⟩
      rw [ht_x, ht_p]
      have h : ((coarse.tube j).base + t_x • (coarse.tube j).direction) -
          ((coarse.tube j).base + t_p • (coarse.tube j).direction) =
          (t_x - t_p) • (coarse.tube j).direction := by
        have h2 : ((coarse.tube j).base + t_x • (coarse.tube j).direction) -
            ((coarse.tube j).base + t_p • (coarse.tube j).direction) =
            t_x • (coarse.tube j).direction - t_p • (coarse.tube j).direction := by abel
        rw [h2, ← sub_smul] <;> rfl
      rw [h, hdir_j_def]
    rcases h_line_diff with ⟨t, ht_eq⟩
    have h_diff : x - p = (x - r_x) + t • dir_j + (r_p - p) := by
      calc
        x - p = (x - r_x) + (r_x - r_p) + (r_p - p) := by abel
        _ = (x - r_x) + t • dir_j + (r_p - p) := by rw [ht_eq] <;> abel
    have h_box_bounds : ∀ (k : Fin 3), |x k| ≤ 1 ∧ |p k| ≤ 1 := by
      have hx' : |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hx_box
      have hp' : |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hp_box
      intro k; fin_cases k <;> tauto
    have h1 : ∀ (k : Fin 3), |x k - p k| ≤ 2 := by
      intro k
      have h2 : |x k| ≤ 1 := (h_box_bounds k).1
      have h3 : |p k| ≤ 1 := (h_box_bounds k).2
      calc
        |x k - p k| ≤ |x k| + |p k| := abs_sub _ _
        _ ≤ 2 := by linarith
    have h2 : ‖x - p‖ ^ 2 =
        (x 0 - p 0)^2 + (x 1 - p 1)^2 + (x 2 - p 2)^2 :=
      point3_norm_sq (x - p)
    have h3 : ‖x - p‖ ^ 2 ≤ 12 := by
      rw [h2]
      have h4 : ∀ k : Fin 3, (x k - p k)^2 ≤ 4 := by
        intro k
        have h5 : |x k - p k| ≤ 2 := h1 k
        have h6 : -2 ≤ x k - p k := (abs_le.mp h5).1
        have h7 : x k - p k ≤ 2 := (abs_le.mp h5).2
        nlinarith
      nlinarith [h4 0, h4 1, h4 2]
    have h4 : 0 ≤ ‖x - p‖ := by positivity
    have h_sqrt : (2 * Real.sqrt 3) ^ 2 = 12 := by
      calc
        (2 * Real.sqrt 3) ^ 2 = 4 * (Real.sqrt 3) ^ 2 := by ring
        _ = 4 * 3 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
        _ = 12 := by norm_num
    have h6 : ‖x - p‖ ^ 2 ≤ (2 * Real.sqrt 3) ^ 2 := by
      rw [h_sqrt]; exact h3
    have h_box_dist : ‖x - p‖ ≤ 2 * Real.sqrt 3 := by
      have h7 : 0 ≤ 2 * Real.sqrt 3 := by positivity
      nlinarith [h4, h7, h6]
    have h_abs_t : |t| ≤ 2 * Real.sqrt 3 + 12 * L := by
      have h5 : t • dir_j = (x - p) - (x - r_x) - (r_p - p) := by
        rw [h_diff] <;> abel
      have h6 : ‖t • dir_j‖ = |t| := by
        rw [norm_smul, hdir_j_unit, Real.norm_eq_abs] <;> ring
      have h7 : ‖(x - p) - (x - r_x) - (r_p - p)‖ ≤ ‖x - p‖ + ‖x - r_x‖ + ‖r_p - p‖ := by
        have h71 : ‖(x - p) - (x - r_x)‖ ≤ ‖x - p‖ + ‖x - r_x‖ :=
          norm_sub_le (x - p) (x - r_x)
        have h72 : ‖(x - p) - (x - r_x) - (r_p - p)‖ ≤ ‖(x - p) - (x - r_x)‖ + ‖r_p - p‖ :=
          norm_sub_le ((x - p) - (x - r_x)) (r_p - p)
        linarith
      calc
        |t| = ‖t • dir_j‖ := h6.symm
        _ = ‖(x - p) - (x - r_x) - (r_p - p)‖ := by rw [h5]
        _ ≤ ‖x - p‖ + ‖x - r_x‖ + ‖r_p - p‖ := h7
        _ ≤ (2 * Real.sqrt 3) + (6 * L) + (6 * L) := by gcongr <;> linarith
        _ = 2 * Real.sqrt 3 + 12 * L := by ring
    have h_t_bound : |t| ≤ 4 := by
      calc
        |t| ≤ 2 * Real.sqrt 3 + 12 * L := h_abs_t
        _ ≤ 2 * Real.sqrt 3 + 12 * (1 / 10000 : ℝ) := by gcongr <;> linarith
        _ ≤ 4 := by
          have h7 : Real.sqrt 3 ≤ 175 / 100 := by
            rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
          linarith
    set u := inner ℝ (x - r_x) dir_i with hu_def
    set v := t * inner ℝ dir_j dir_i with hv_def
    set w := inner ℝ (r_p - p) dir_i with hw_def
    have h1 : |u| ≤ ‖x - r_x‖ := by
      have h1' : |u| ≤ ‖x - r_x‖ * ‖dir_i‖ := abs_real_inner_le_norm _ _
      rw [hdir_i_unit] at h1'; simpa using h1'
    have h2 : |v| ≤ |t| * ‖dir_j‖ := by
      have h21 : |inner ℝ dir_j dir_i| ≤ ‖dir_j‖ * ‖dir_i‖ := abs_real_inner_le_norm _ _
      rw [hdir_i_unit] at h21
      have h22 : |v| = |t| * |inner ℝ dir_j dir_i| := by
        simpa [hv_def, abs_mul] using rfl
      rw [h22]; gcongr <;> linarith
    have h3 : |w| ≤ ‖r_p - p‖ := by
      have h3' : |w| ≤ ‖r_p - p‖ * ‖dir_i‖ := abs_real_inner_le_norm _ _
      rw [hdir_i_unit] at h3'; simpa using h3'
    have h_axial : |inner ℝ (x - p) dir_i| ≤ a0 := by
      have h_inner : inner ℝ (x - p) dir_i = u + v + w := by
        rw [h_diff]
        simp [u, v, w, inner_add_left, inner_smul_left] <;> ring
      rw [h_inner]
      have h4 : |u + v + w| ≤ |u| + |v| + |w| := by
        calc
          |u + v + w| = |(u + v) + w| := by rw [add_assoc]
          _ ≤ |u + v| + |w| := abs_add_le _ _
          _ ≤ |u| + |v| + |w| := by gcongr; exact abs_add_le _ _
      have h5 : |u| + |v| + |w| ≤ ‖x - r_x‖ + |t| * ‖dir_j‖ + ‖r_p - p‖ := by
        gcongr <;> linarith
      have h6 : ‖x - r_x‖ + |t| * ‖dir_j‖ + ‖r_p - p‖ ≤ (6 * L) + 4 * 1 + (6 * L) := by
        have h61 : ‖x - r_x‖ ≤ 6 * L := hr_x_norm
        have h62 : |t| * ‖dir_j‖ ≤ 4 * 1 := by
          have h63 : ‖dir_j‖ = 1 := hdir_j_unit
          rw [h63]
          have h64 : |t| ≤ 4 := h_t_bound
          nlinarith
        have h65 : ‖r_p - p‖ ≤ 6 * L := hr_p_norm
        linarith
      calc
        |u + v + w| ≤ |u| + |v| + |w| := h4
        _ ≤ ‖x - r_x‖ + |t| * ‖dir_j‖ + ‖r_p - p‖ := h5
        _ ≤ (6 * L) + 4 * 1 + (6 * L) := h6
        _ = 12 * L + 4 := by ring
        _ ≤ a0 := by simp [a0] <;> linarith [hL_small]
    let radial := fun (z : Point3) => z - inner ℝ z dir_i • dir_i
    have h_radial_diff : radial (x - p) =
        radial (x - r_x) + t • radial dir_j + radial (r_p - p) :=
      perp_projection_radial_diff dir_i x p r_x r_p dir_j t h_diff
    have h_radial_dir_j_norm : ‖radial dir_j‖ = ‖wz1Cross dir_i dir_j‖ := by
      have h_comm : inner ℝ dir_j dir_i = inner ℝ dir_i dir_j := real_inner_comm _ _
      have h_radial_eq : radial dir_j = dir_j - inner ℝ dir_i dir_j • dir_i := by
        dsimp only [radial]
        rw [h_comm]
      rw [h_radial_eq]
      exact (radial_norm_eq_cross_norm hdir_i_unit hdir_j_unit).symm
    have h_radial_e1_norm : ‖radial (x - r_x)‖ ≤ ‖x - r_x‖ := by
      dsimp only [radial]
      exact perp_projection_contractive hdir_i_unit
    have h_radial_e2_norm : ‖radial (r_p - p)‖ ≤ ‖r_p - p‖ := by
      dsimp only [radial]
      exact perp_projection_contractive hdir_i_unit
    have h_radial_bound : ‖radial (x - p)‖ ≤ a1 := by
      rw [h_radial_diff]
      have h4 : ‖radial (x - r_x)‖ ≤ 6 * L := by
        calc ‖radial (x - r_x)‖ ≤ ‖x - r_x‖ := h_radial_e1_norm
             _ ≤ 6 * L := hr_x_norm
      have h5 : ‖radial (r_p - p)‖ ≤ 6 * L := by
        calc ‖radial (r_p - p)‖ ≤ ‖r_p - p‖ := h_radial_e2_norm
             _ ≤ 6 * L := hr_p_norm
      have h6 : ‖t • radial dir_j‖ = |t| * ‖radial dir_j‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      calc
        ‖radial (x - r_x) + t • radial dir_j + radial (r_p - p)‖
          ≤ ‖radial (x - r_x) + t • radial dir_j‖ + ‖radial (r_p - p)‖ := norm_add_le _ _
        _ ≤ ‖radial (x - r_x)‖ + ‖t • radial dir_j‖ + ‖radial (r_p - p)‖ := by
          gcongr; exact norm_add_le _ _
        _ = ‖radial (x - r_x)‖ + |t| * ‖radial dir_j‖ + ‖radial (r_p - p)‖ := by
          rw [h6] <;> ring
        _ = ‖radial (x - r_x)‖ + |t| * ‖wz1Cross dir_i dir_j‖ + ‖radial (r_p - p)‖ := by
          rw [h_radial_dir_j_norm] <;> ring
        _ ≤ (6 * L) + |t| * ‖wz1Cross dir_i dir_j‖ + (6 * L) := by gcongr <;> linarith
        _ ≤ (6 * L) + 4 * kappa + (6 * L) := by gcongr <;> linarith [hj_cross.le]
        _ = 12 * L + 4 * kappa := by ring
        _ ≤ 16 * kappa := by
          have h9 : 12 * L ≤ 12 * kappa := by gcongr
          linarith
        _ = a1 := by simp [a1]
    have h_coord0 : |(A (x - p)) 0| ≤ a0 := by
      rw [hcoord0] <;> exact h_axial
    have h_perp_sq :
        |(A (x - p)) 1| ^ 2 + |(A (x - p)) 2| ^ 2 ≤ a1 ^ 2 := by
      have h : ‖radial (x - p)‖ ^ 2 =
          |(A (x - p)) 1| ^ 2 + |(A (x - p)) 2| ^ 2 := hcoord_perp (x - p)
      have h' : ‖radial (x - p)‖ ^ 2 ≤ a1 ^ 2 := by gcongr
      rw [h] at h'; exact h'
    have h_coord1 : |(A (x - p)) 1| ≤ a1 := by
      have h1 : |(A (x - p)) 1| ^ 2 ≤ a1 ^ 2 := by
        have h_sum : |(A (x - p)) 1| ^ 2 ≤ |(A (x - p)) 1| ^ 2 + |(A (x - p)) 2| ^ 2 :=
          le_add_of_nonneg_right (sq_nonneg _)
        exact le_trans h_sum h_perp_sq
      have h2 : 0 ≤ |(A (x - p)) 1| := by positivity
      have h3 : 0 ≤ a1 := by positivity
      nlinarith
    have h_coord2 : |(A (x - p)) 2| ≤ a2 := by
      have h1 : |(A (x - p)) 2| ^ 2 ≤ a1 ^ 2 := by
        have h_sum : |(A (x - p)) 2| ^ 2 ≤ |(A (x - p)) 1| ^ 2 + |(A (x - p)) 2| ^ 2 :=
          le_add_of_nonneg_left (sq_nonneg _)
        exact le_trans h_sum h_perp_sq
      have h2 : 0 ≤ |(A (x - p)) 2| := by positivity
      have h3 : 0 ≤ a1 := by positivity
      have h4 : a2 = a1 := by simp [a1, a2]
      rw [h4]
      nlinarith
    exact ⟨h_coord0, h_coord1, h_coord2⟩
  let closeSet : Finset (Fin coarse.card) :=
    Finset.univ.filter fun j =>
      p ∈ coarseShading.carrier j ∧
        ‖wz1Cross dir_i (coarse.tube j).direction‖ < kappa
  have h_closeSet_eq : closeSet.card = paperCloseDirectionCount coarseShading p i kappa := by
    rfl
  have h_subset : closeSet ⊆ (wz1PaperBodyFamily coarse).containedIndices W := by
    intro j hj
    have h1 : p ∈ coarseShading.carrier j ∧
        ‖wz1Cross dir_i (coarse.tube j).direction‖ < kappa :=
      (Finset.mem_filter.mp hj).2
    have h2 : wz1PaperTubeCarrier (coarse.tube j) ⊆ W :=
      h_containment j h1.1 h1.2
    have h3 : ((wz1PaperBodyFamily coarse).body j).carrier = wz1PaperTubeCarrier (coarse.tube j) := by
      rfl
    have h4 : ((wz1PaperBodyFamily coarse).body j).carrier ⊆ W := by
      rw [h3]
      exact h2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h4⟩
  have h_card : closeSet.card ≤ ((wz1PaperBodyFamily coarse).containedIndices W).card :=
    Finset.card_le_card h_subset
  have h_count_le : (closeSet.card : ENNReal) ≤ (wz1PaperBodyFamily coarse).containedCount W := by
    dsimp only [Kakeya.Streamlined.BodyFamily.containedCount]
    exact_mod_cast h_card
  have hCWA' := hCWA W hW_convex
  have h_final : (closeSet.card : ENNReal) ≤
      C * volume W * coarse.enncard := by
    calc
      (closeSet.card : ENNReal)
          ≤ (wz1PaperBodyFamily coarse).containedCount W := h_count_le
      _ ≤ C * volume W * coarse.enncard := hCWA'
  have h_final2 : (closeSet.card : ENNReal) ≤
      C * ENNReal.ofReal (10000 * kappa^2) * coarse.enncard := by
    calc
      (closeSet.card : ENNReal)
          ≤ C * volume W * coarse.enncard := h_final
      _ ≤ C * (ENNReal.ofReal (10000 * kappa^2)) * coarse.enncard := by
        gcongr <;> exact h_volume
  rw [h_closeSet_eq] at h_final2
  exact h_final2

/-- Prove the `hclose_band` hypothesis of `fiber_scale_weak_map` from a
Convex-Wolff bound on the family.

For any subshading `S_cm`, the close-direction count is bounded by the CWA bound
applied directly to `S_cm` (CWA is a family-level property). Requires `κ ≥ L`
and `C * 10000 * κ² * N < R`. -/
lemma hclose_band_from_cwa
    {L : ℝ}
    {F : Kakeya.Streamlined.TubeFamily L}
    {S : WZ1PaperTubeShading F}
    {C : ENNReal}
    (hCWA : WZ2PaperConvexWolffBound F C)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 10000)
    (kappa : ℝ)
    (hkappa_pos : 0 < kappa)
    (hkappa_le_one : kappa ≤ 1)
    (hkappa_ge_L : L ≤ kappa)
    (R : ℕ)
    (hR : C * ENNReal.ofReal (10000 * kappa^2) * F.enncard < (R : ENNReal)) :
    ∀ (S_cm : WZ1PaperTubeShading F),
      PaperIsSubshading S_cm S →
      ∀ p ∈ S_cm.union, ∀ i,
        p ∈ S_cm.carrier i →
          paperCloseDirectionCount S_cm p i kappa < R := by
  intro S_cm hsub p hp i hi
  have h1 : (paperCloseDirectionCount S_cm p i kappa : ENNReal) ≤
      C * ENNReal.ofReal (10000 * kappa^2) * F.enncard :=
    paper_cwa_close_direction_count
      hCWA hL_pos hL_small kappa hkappa_pos hkappa_le_one hkappa_ge_L p i hi
  have h2 : (paperCloseDirectionCount S_cm p i kappa : ENNReal) < (R : ENNReal) :=
    lt_of_le_of_lt h1 hR
  exact_mod_cast h2

end Kakeya.Assouad

end
