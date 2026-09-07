import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# Axis zero-point bounds under anisotropic rescaling

Given an original tube in the WZ1 paper line class, bound the x and y
coordinates of the anisotropically rescaled tube's axis zero point.

The rescaled zero point corresponds to the original axis point at height
z = c + (d-c)/2 (the midpoint of [c,d]), mapped through Φ.

Bounds:
- |x'| ≤ 14/3 (exactly what line_class_pigeonhole_selection needs)
- |y'| ≤ 7/150 (exactly what line_class_pigeonhole_selection needs)

## Whiteprint node
TransferLineClass — depends on ConstructRescaledFamily, LineClassPigeonholeSelection.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The point on the original tube axis at height z. -/
def axisPointAtHeight {delta : ℝ} (tube : Kakeya.DeltaTube delta) (z : ℝ) : Point3 :=
  tube.base + ((z - tube.base 2) / tube.direction 2) • tube.direction

lemma axisPointAtHeight_z
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hvertical : (1 / 2 : ℝ) ≤ |tube.direction 2|)
    (z : ℝ) :
    (axisPointAtHeight tube z) 2 = z := by
  have hne : tube.direction 2 ≠ 0 := by
    intro h; rw [h, abs_zero] at hvertical; norm_num at hvertical
  simp [axisPointAtHeight, hne]

/-- |direction i| ≤ 1 since ‖direction‖ = 1. -/
lemma dir_coord_abs_le_one
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (i : Fin 3) :
    |tube.direction i| ≤ 1 := by
  have h1 : (tube.direction i) ^ 2 ≤ ‖tube.direction‖ ^ 2 := by
    have h2 : ‖tube.direction‖ ^ 2 = ∑ j : Fin 3, (tube.direction j) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq tube.direction
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : |tube.direction i| ^ 2 ≤ ‖tube.direction‖ ^ 2 := by
    simpa [sq_abs] using h1
  have h4 : 0 ≤ |tube.direction i| := abs_nonneg _
  have h5 : 0 ≤ ‖tube.direction‖ := norm_nonneg _
  have h6 : |tube.direction i| ≤ ‖tube.direction‖ := by
    have h7 : |(|tube.direction i|)| ≤ |‖tube.direction‖| := sq_le_sq.mp h3
    simpa [abs_of_nonneg h4, abs_of_nonneg h5] using h7
  have h8 : ‖tube.direction‖ = 1 := tube.direction_unit
  rw [h8] at h6
  exact h6

/-- Bound |p_x| ≤ 7/3 for axis point at height |z| ≤ 1. -/
lemma axisPointAtHeight_x_bound
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (h_line : WZ1PaperTubeInLineClass tube)
    (z : ℝ) (hz_abs : |z| ≤ 1) :
    |(axisPointAtHeight tube z) 0| ≤ 7 / 3 := by
  have hne : tube.direction 2 ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ |tube.direction 2| := h_line.vertical
    intro h2; rw [h2, abs_zero] at h; norm_num at h
  have hdir2_abs : (1 / 2 : ℝ) ≤ |tube.direction 2| := h_line.vertical
  have hzero_x : |wz1TubeAxisZeroPoint tube 0| ≤ 1 / 3 := h_line.2.1
  have hdir0_abs : |tube.direction 0| ≤ 1 := dir_coord_abs_le_one tube 0
  have h_decomp : (axisPointAtHeight tube z) 0 =
      wz1TubeAxisZeroPoint tube 0 + (z / tube.direction 2) * tube.direction 0 := by
    simp [axisPointAtHeight, wz1TubeAxisZeroPoint] ; ring
  rw [h_decomp]
  have h_ratio : |z| / |tube.direction 2| ≤ 2 := by
    have h5 : |z| ≤ 1 := hz_abs
    have h6 : (1 / 2 : ℝ) ≤ |tube.direction 2| := hdir2_abs
    calc |z| / |tube.direction 2|
      ≤ 1 / |tube.direction 2| := by gcongr
    _ ≤ 1 / (1 / 2 : ℝ) := by gcongr
    _ = 2 := by norm_num
  have h_product : |z| / |tube.direction 2| * |tube.direction 0| ≤ 2 := by
    calc |z| / |tube.direction 2| * |tube.direction 0|
      ≤ 2 * 1 := by gcongr
    _ = 2 := by norm_num
  have h_tri : |wz1TubeAxisZeroPoint tube 0 + (z / tube.direction 2) * tube.direction 0| ≤
      |wz1TubeAxisZeroPoint tube 0| + |z| / |tube.direction 2| * |tube.direction 0| := by
    have h_abs2 : |(z / tube.direction 2) * tube.direction 0| =
        |z| / |tube.direction 2| * |tube.direction 0| := by
      rw [abs_mul, abs_div]
    have h : |wz1TubeAxisZeroPoint tube 0 + (z / tube.direction 2) * tube.direction 0| ≤
        |wz1TubeAxisZeroPoint tube 0| + |(z / tube.direction 2) * tube.direction 0| := by
      exact abs_add_le _ _
    rw [h_abs2] at h
    exact h
  linarith

/-- Bound |p_y| ≤ 7/3 for axis point at height |z| ≤ 1. -/
lemma axisPointAtHeight_y_bound
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (h_line : WZ1PaperTubeInLineClass tube)
    (z : ℝ) (hz_abs : |z| ≤ 1) :
    |(axisPointAtHeight tube z) 1| ≤ 7 / 3 := by
  have hne : tube.direction 2 ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ |tube.direction 2| := h_line.vertical
    intro h2; rw [h2, abs_zero] at h; norm_num at h
  have hdir2_abs : (1 / 2 : ℝ) ≤ |tube.direction 2| := h_line.vertical
  have hzero_y : |wz1TubeAxisZeroPoint tube 1| ≤ 1 / 3 := h_line.2.2
  have hdir1_abs : |tube.direction 1| ≤ 1 := dir_coord_abs_le_one tube 1
  have h_decomp : (axisPointAtHeight tube z) 1 =
      wz1TubeAxisZeroPoint tube 1 + (z / tube.direction 2) * tube.direction 1 := by
    simp [axisPointAtHeight, wz1TubeAxisZeroPoint] ; ring
  rw [h_decomp]
  have h_ratio : |z| / |tube.direction 2| ≤ 2 := by
    have h5 : |z| ≤ 1 := hz_abs
    have h6 : (1 / 2 : ℝ) ≤ |tube.direction 2| := hdir2_abs
    calc |z| / |tube.direction 2|
      ≤ 1 / |tube.direction 2| := by gcongr
    _ ≤ 1 / (1 / 2 : ℝ) := by gcongr
    _ = 2 := by norm_num
  have h_product : |z| / |tube.direction 2| * |tube.direction 1| ≤ 2 := by
    calc |z| / |tube.direction 2| * |tube.direction 1|
      ≤ 2 * 1 := by gcongr
    _ = 2 := by norm_num
  have h_tri : |wz1TubeAxisZeroPoint tube 1 + (z / tube.direction 2) * tube.direction 1| ≤
      |wz1TubeAxisZeroPoint tube 1| + |z| / |tube.direction 2| * |tube.direction 1| := by
    have h_abs2 : |(z / tube.direction 2) * tube.direction 1| =
        |z| / |tube.direction 2| * |tube.direction 1| := by
      rw [abs_mul, abs_div]
    have h : |wz1TubeAxisZeroPoint tube 1 + (z / tube.direction 2) * tube.direction 1| ≤
        |wz1TubeAxisZeroPoint tube 1| + |(z / tube.direction 2) * tube.direction 1| := by
      exact abs_add_le _ _
    rw [h_abs2] at h
    exact h
  linarith

/--
Bound the x-coordinate of the anisotropically rescaled zero point.
|x'| = |p_x + g(z_mid) * p_y| ≤ 7/3 + 7/3 = 14/3
-/
lemma anisotropicRescaledZeroPoint_x_bound
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (g : SlopeFunction) (hg_norm : g.IsNormalized)
    (c d : ℝ) (hcd : c < d)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (h_line : WZ1PaperTubeInLineClass tube) :
    let z_mid := c + (d - c) / 2
    let p := axisPointAtHeight tube z_mid
    |p 0 + g z_mid * p 1| ≤ 14 / 3 := by
  let z_mid := c + (d - c) / 2
  have hc_in : c ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
  have hd_in : d ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
  have h1 : -1 ≤ c := (h_sub hc_in).1
  have h2 : d ≤ 1 := (h_sub hd_in).2
  have h3 : c ≤ z_mid := by
    dsimp only [z_mid]
    linarith
  have h4 : z_mid ≤ d := by
    dsimp only [z_mid]
    linarith
  have h5 : -1 ≤ z_mid := by linarith
  have h6 : z_mid ≤ 1 := by linarith
  have hmid_in : z_mid ∈ Set.Icc (-1 : ℝ) 1 := ⟨h5, h6⟩
  have hz_abs : |z_mid| ≤ 1 := abs_le.mpr ⟨h5, h6⟩
  have hg_abs : |g z_mid| ≤ 1 := (hg_norm z_mid hmid_in).1
  let p := axisPointAtHeight tube z_mid
  have hpx : |p 0| ≤ 7 / 3 := axisPointAtHeight_x_bound h_line z_mid hz_abs
  have hpy : |p 1| ≤ 7 / 3 := axisPointAtHeight_y_bound h_line z_mid hz_abs
  have h_tri : |p 0 + g z_mid * p 1| ≤ |p 0| + |g z_mid * p 1| := by
    exact abs_add_le _ _
  have h_abs : |g z_mid * p 1| = |g z_mid| * |p 1| := by rw [abs_mul]
  have h_prod : |g z_mid| * |p 1| ≤ 7 / 3 := by
    calc |g z_mid| * |p 1|
      ≤ 1 * |p 1| := by gcongr
    _ = |p 1| := by ring
    _ ≤ 7 / 3 := hpy
  have h_sum : |p 0| + |g z_mid| * |p 1| ≤ 14 / 3 := by linarith
  have h_final : |p 0 + g z_mid * p 1| ≤ 14 / 3 := by
    calc |p 0 + g z_mid * p 1|
      ≤ |p 0| + |g z_mid * p 1| := h_tri
    _ = |p 0| + |g z_mid| * |p 1| := by rw [h_abs]
    _ ≤ 14 / 3 := h_sum
  exact h_final

/--
Bound the y-coordinate of the anisotropically rescaled zero point.
|y'| = m*(d-c)/2 * |p_y| ≤ 1*(1/25)/2 * 7/3 = 7/150
-/
lemma anisotropicRescaledZeroPoint_y_bound
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (c d m : ℝ) (hcd : c < d) (hm_pos : 0 < m) (hm_le_one : m ≤ 1)
    (h_len : d - c ≤ 1 / 25)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (h_line : WZ1PaperTubeInLineClass tube) :
    let z_mid := c + (d - c) / 2
    let p := axisPointAtHeight tube z_mid
    |m * (d - c) / 2 * p 1| ≤ 7 / 150 := by
  let z_mid := c + (d - c) / 2
  have hc_in : c ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
  have hd_in : d ∈ Set.Icc c d := ⟨by linarith, by linarith⟩
  have h1 : -1 ≤ c := (h_sub hc_in).1
  have h2 : d ≤ 1 := (h_sub hd_in).2
  have h3 : c ≤ z_mid := by
    dsimp only [z_mid]
    linarith
  have h4 : z_mid ≤ d := by
    dsimp only [z_mid]
    linarith
  have h5 : -1 ≤ z_mid := by linarith
  have h6 : z_mid ≤ 1 := by linarith
  have hmid_in : z_mid ∈ Set.Icc (-1 : ℝ) 1 := ⟨h5, h6⟩
  have hz_abs : |z_mid| ≤ 1 := abs_le.mpr ⟨h5, h6⟩
  let p := axisPointAtHeight tube z_mid
  have hpy : |p 1| ≤ 7 / 3 := axisPointAtHeight_y_bound h_line z_mid hz_abs
  have hK_nonneg : 0 ≤ m * (d - c) / 2 := by positivity
  have h_abs : |m * (d - c) / 2 * p 1| = m * (d - c) / 2 * |p 1| := by
    rw [abs_mul, abs_of_nonneg hK_nonneg]
  have h_main : m * (d - c) / 2 * |p 1| ≤ 7 / 150 := by
    calc
      m * (d - c) / 2 * |p 1|
        ≤ 1 * (1 / 25) / 2 * (7 / 3) := by gcongr
      _ = 7 / 150 := by norm_num
  have h_goal : |m * (d - c) / 2 * p 1| ≤ 7 / 150 := by
    rw [h_abs]
    exact h_main
  exact h_goal

end Kakeya.Assouad

end
