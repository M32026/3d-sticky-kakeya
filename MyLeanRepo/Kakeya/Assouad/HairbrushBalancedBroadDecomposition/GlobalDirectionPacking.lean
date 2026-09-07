import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.Hairbrush.AcuteAngleHelpers
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MultiplicityBound
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Global direction packing for large theta

Provides `global_direction_packing`: theta-separated unit vectors have
cardinality ≤1000 for 1/6 ≤ theta ≤ 1/2.
-/

noncomputable section

open Metric Finset InnerProductGeometry Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- For unit vectors, Euclidean angle equals arccos of inner product. -/
private lemma unit_angle_eq_arccos'' {v u : Point3} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    angle v u = Real.arccos (inner ℝ v u) := by
  have h1 : Real.cos (angle v u) * (‖v‖ * ‖u‖) = inner ℝ v u :=
    cos_angle_mul_norm_mul_norm v u
  have h2 : Real.cos (angle v u) = inner ℝ v u := by
    rw [hv, hu] at h1; norm_num at h1 ⊢; exact h1
  have h3 : 0 ≤ angle v u := angle_nonneg v u
  have h4 : angle v u ≤ Real.pi := angle_le_pi v u
  have h5 : Real.arccos (Real.cos (angle v u)) = angle v u := Real.arccos_cos h3 h4
  rw [h2] at h5; exact h5.symm

/-- Euclidean distance = 2*sin(angle/2) for unit vectors. -/
private lemma dist_eq_two_sin_half_angle {v w : Point3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    dist v w = 2 * Real.sin (angle v w / 2) := by
  have h1 : dist v w = ‖v - w‖ := by rfl
  rw [h1]
  set ang : ℝ := angle v w with hang
  have h3 : inner ℝ v w = Real.cos ang := by
    have h4 : ang = Real.arccos (inner ℝ v w) := unit_angle_eq_arccos'' hv hw
    rw [h4]
    have h5 : -1 ≤ inner ℝ v w ∧ inner ℝ v w ≤ 1 := by
      have h6 : |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
      rw [hv, hw] at h6; exact ⟨by linarith [abs_le.mp h6], by linarith [abs_le.mp h6]⟩
    rw [Real.cos_arccos h5.1 h5.2]
  have h6 : Real.cos ang = 1 - 2 * Real.sin (ang / 2) ^ 2 := by
    have h7 : Real.cos (2 * (ang / 2)) = 2 * Real.cos (ang / 2) ^ 2 - 1 := Real.cos_two_mul (ang / 2)
    have h8 : 2 * (ang / 2) = ang := by ring
    rw [h8] at h7
    have h9 : Real.cos (ang / 2) ^ 2 = 1 - Real.sin (ang / 2) ^ 2 := by
      rw [Real.sin_sq]; ring
    rw [h9] at h7; linarith
  have h10 : 0 ≤ Real.sin (ang / 2) := Real.sin_nonneg_of_mem_Icc ⟨by linarith [angle_nonneg v w], by linarith [Real.pi_pos, angle_le_pi v w]⟩
  have h11 : ‖v - w‖ ^ 2 = (2 * Real.sin (ang / 2)) ^ 2 := by
    have h2 : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2 := norm_sub_sq_real v w
    rw [h2, hv, hw, h3, h6]; ring
  have h12 : 0 ≤ ‖v - w‖ := by positivity
  nlinarith

/-- Euclidean distance lower bound from acute angle separation. -/
private lemma acute_to_dist_lower' {v w : Point3}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {theta : ℝ} (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (h : theta ≤ hairbrushAcuteDirectionAngle v w) :
    2 * Real.sin (theta / 2) ≤ dist v w := by
  set ang : ℝ := angle v w with hang_def
  have h_ang_le_pi : ang ≤ Real.pi := angle_le_pi v w
  by_cases h_case : ang ≤ Real.pi / 2
  · have h_acute_eq : hairbrushAcuteDirectionAngle v w = ang := by
      have h_arccos : ang = Real.arccos (inner ℝ v w) := unit_angle_eq_arccos'' hv hw
      dsimp only [hairbrushAcuteDirectionAngle]
      rw [h_arccos]; rw [min_eq_left] <;> linarith
    have h_ang_ge : theta ≤ ang := by rw [h_acute_eq] at h; exact h
    have h_sin_ge : Real.sin (theta / 2) ≤ Real.sin (ang / 2) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith [Real.pi_pos]) (by linarith)
    rw [dist_eq_two_sin_half_angle hv hw]; gcongr
  · have h_gt : Real.pi / 2 < ang := by linarith
    have h_ang2_le : ang / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have h_sin_gt : Real.sin (ang / 2) > Real.sqrt 2 / 2 := by
      have h1 : ang / 2 > Real.pi / 4 := by linarith [Real.pi_pos]
      have h3 : Real.sin (Real.pi / 4) < Real.sin (ang / 2) :=
        Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) h_ang2_le h1
      have h4 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := by rw [Real.sin_pi_div_four]
      rw [h4] at h3; exact h3
    have h_sin_le : 2 * Real.sin (theta / 2) ≤ theta := by
      have h5 : Real.sin (theta / 2) ≤ theta / 2 := Real.sin_le (by linarith)
      linarith
    have h_main : 2 * Real.sin (theta / 2) < 2 * Real.sin (ang / 2) := by
      have h6 : 2 * Real.sin (theta / 2) ≤ theta := h_sin_le
      have h7 : theta ≤ 1 := htheta1
      have h8 : (1 : ℝ) < Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h9 : 2 * Real.sin (theta / 2) < Real.sqrt 2 := by linarith
      have h10 : Real.sqrt 2 < 2 * Real.sin (ang / 2) := by linarith [h_sin_gt]
      linarith
    rw [dist_eq_two_sin_half_angle hv hw]; exact h_main.le

/-- Global packing bound: theta-separated unit vectors have cardinality ≤1000
for 1/6 ≤ theta ≤ 1/2. -/
lemma global_direction_packing {theta : ℝ} (htheta : 1 / 6 ≤ theta) (htheta2 : theta ≤ 1 / 2)
    {s : Finset Point3} (hs1 : ∀ v ∈ s, ‖v‖ = 1)
    (hs2 : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → theta ≤ hairbrushAcuteDirectionAngle v w) :
    s.card ≤ 1000 := by
  set ε : ℝ := 2 * Real.sin (theta / 2) with hε_def
  have hε_pos : 0 < ε := by
    have h1 : 0 < theta / 2 := by linarith
    have h2 : theta / 2 < Real.pi := by
      have h3 : theta ≤ 1 / 2 := htheta2
      have h4 : Real.pi > 3 := Real.pi_gt_three
      linarith
    have h5 : 0 < Real.sin (theta / 2) := Real.sin_pos_of_pos_of_lt_pi h1 h2
    positivity
  have hε_le1 : ε ≤ 1 := by
    have h1 : Real.sin (theta / 2) ≤ theta / 2 := Real.sin_le (by linarith)
    calc ε
      = 2 * Real.sin (theta / 2) := by rfl
    _ ≤ 2 * (theta / 2) := by gcongr
    _ = theta := by ring
    _ ≤ 1 / 2 := htheta2
    _ ≤ 1 := by norm_num
  have h_dist_sep : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → ε ≤ dist v w := by
    intro v hv w hw hne
    have h1 : theta ≤ hairbrushAcuteDirectionAngle v w := hs2 v hv w hw hne
    exact acute_to_dist_lower' (hs1 v hv) (hs1 w hw) (by linarith) (by linarith) h1
  have h_pack : (s.card : ℝ) ≤ 26 / ε ^ 2 :=
    sphere_separated_card_bound_annulus hε_pos hε_le1 hs1 h_dist_sep
  have h_sin_lower : Real.sin (theta / 2) ≥ Real.sin (1 / 12 : ℝ) := by
    have h1 : 1 / 12 ≤ theta / 2 := by linarith
    have h2 : theta / 2 ≤ 1 / 4 := by linarith
    have hpi : Real.pi > 3 := Real.pi_gt_three
    have h3 : theta / 2 ≤ Real.pi / 2 := by linarith
    have h4 : -(Real.pi / 2) ≤ (1 / 12 : ℝ) := by
      have h5 : 0 < Real.pi / 2 := by positivity
      linarith
    exact Real.sin_le_sin_of_le_of_le_pi_div_two h4 h3 h1
  have h_ε_lower : ε ≥ 2 * Real.sin (1 / 12 : ℝ) := by
    rw [hε_def] <;> gcongr
  have h_sin12_lower : Real.sin (1 / 12 : ℝ) > (1 / 12 : ℝ) - (1 / 12 : ℝ)^3 / 4 :=
    Real.sin_gt_sub_cube (by norm_num) (by norm_num)
  have h4 : 2 * Real.sin (1 / 12 : ℝ) > 575 / 3456 := by
    have h5 : Real.sin (1 / 12 : ℝ) > 575 / 6912 := by linarith [h_sin12_lower]
    linarith
  have h6 : ε > 575 / 3456 := by linarith
  have h7 : 26 / ε ^ 2 ≤ 1000 := by
    have h8 : 0 < ε := hε_pos
    have h9 : ε ^ 2 > (575 / 3456 : ℝ)^2 := by gcongr
    have h10 : 26 / ε ^ 2 ≤ 26 / (575 / 3456 : ℝ)^2 := by gcongr
    have h11 : 26 / (575 / 3456 : ℝ)^2 ≤ 1000 := by norm_num
    linarith
  have h12 : (s.card : ℝ) ≤ 1000 := by
    calc (s.card : ℝ)
      ≤ 26 / ε ^ 2 := h_pack
    _ ≤ 1000 := h7
  exact_mod_cast h12

end Kakeya.Assouad
