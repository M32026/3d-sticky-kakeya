import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalSingleBall
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalProjectionHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalSliceGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BoundedIntervalAD
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment
import Mathlib.Tactic

/-!
# Single-tube global AD

Helper lemmas for constructing global AD on a single-tube configuration.

## Key insight

For a single tube of width `L` with direction `d` (line-class, `|d 2| ≥ 1/2`):
1. The horizontal slice at height `z` has diameter `≤ 4L`, fitting in `B(p, √L)` for `L ≤ 1/16`.
2. The horizontal perpendicular `v = (-d 1, d 0, 0) / √(d 0² + d 1²)` satisfies:
   - `‖v‖ = 1`, `v 2 = 0`
   - `inner(d, v) = 0 ≤ L` (incidence)
   - After optional x/y axis swap, `|v 0| ≥ 1/3`
3. With constant `planeMap = v`, `single_ball_global_ad` gives global AD.
4. The factor `100` is absorbed by `L^{-outputLoss}` for small `L`.
-/

noncomputable section

namespace Kakeya.Assouad

open Classical Metric Set

/-- Horizontal perpendicular to a direction `d`.

Given `d` with nonzero horizontal component, returns `v = (-d 1, d 0, 0) / H`
where `H = √(d 0² + d 1²)`. This satisfies `inner(d, v) = 0`, `v 2 = 0`, `‖v‖ = 1`. -/
def horizontalPerpendicular (d : Point3) (_h : d 0 ≠ 0 ∨ d 1 ≠ 0) : Point3 :=
  let H := Real.sqrt (d 0 ^ 2 + d 1 ^ 2)
  point3 (-d 1 / H) (d 0 / H) 0

lemma horizontalPerpendicular_spec (d : Point3) (h : d 0 ≠ 0 ∨ d 1 ≠ 0) :
    let v := horizontalPerpendicular d h
    ‖v‖ = 1 ∧ inner ℝ d v = 0 ∧ v 2 = 0 := by
  let H := Real.sqrt (d 0 ^ 2 + d 1 ^ 2)
  have hH_pos : 0 < H := by
    have h1 : 0 < d 0 ^ 2 + d 1 ^ 2 := by
      cases h with
      | inl h0 => exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (by positivity)
      | inr h1 => exact add_pos_of_nonneg_of_pos (by positivity) (sq_pos_of_ne_zero h1)
    exact Real.sqrt_pos.mpr h1
  have hH2 : H ^ 2 = d 0 ^ 2 + d 1 ^ 2 := Real.sq_sqrt (by positivity)
  set v : Point3 := horizontalPerpendicular d h with hv_def
  have h_v_eq : v = point3 (-d 1 / H) (d 0 / H) 0 := by
    simp [horizontalPerpendicular, hv_def, point3] <;> rfl
  have hv0 : v 0 = -d 1 / H := by rw [h_v_eq] <;> simp [point3]
  have hv1 : v 1 = d 0 / H := by rw [h_v_eq] <;> simp [point3]
  have hv2 : v 2 = 0 := by rw [h_v_eq] <;> simp [point3]
  have h_sum : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    rw [hv0, hv1, hv2]
    have hH2' : d 0 ^ 2 + d 1 ^ 2 = H ^ 2 := hH2.symm
    field_simp [hH_pos.ne', hH2'] <;> ring_nf <;> linarith
  have h_norm2 : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    have h22 : ‖v‖ = Real.sqrt (∑ i : Fin 3, |v i| ^ 2) := EuclideanSpace.norm_eq v
    have h23 : (∑ i : Fin 3, |v i| ^ 2) = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
      simp [Fin.sum_univ_succ, sq_abs] <;> ring
    rw [h22, h23]
    rw [Real.sq_sqrt (by positivity)]
  have h_norm : ‖v‖ = 1 := by
    have h3 : ‖v‖ ^ 2 = 1 := by
      rw [h_norm2, h_sum]
    have h4 : 0 ≤ ‖v‖ := by positivity
    nlinarith
  have h_inner : inner ℝ d v = 0 := by
    have h : inner ℝ d v = d 0 * v 0 + d 1 * v 1 + d 2 * v 2 := by
      simp [PiLp.inner_apply, Fin.sum_univ_succ] <;> ring
    rw [h, hv0, hv1, hv2]
    <;> field_simp [hH_pos.ne'] <;> ring
  exact ⟨h_norm, h_inner, hv2⟩

/-- At least one of `|d 0|` or `|d 1|` is `≥ H / 3` where `H = √(d 0² + d 1²)`.

Since `d 0² + d 1² = H²`, if both were `< H/3`, then `H² < 2H²/9`, contradiction. -/
lemma horizontal_component_bound (d : Point3) (hH : 0 < d 0 ^ 2 + d 1 ^ 2) :
    |d 0| ≥ Real.sqrt (d 0 ^ 2 + d 1 ^ 2) / 3 ∨
    |d 1| ≥ Real.sqrt (d 0 ^ 2 + d 1 ^ 2) / 3 := by
  let H := Real.sqrt (d 0 ^ 2 + d 1 ^ 2)
  have hH2 : H ^ 2 = d 0 ^ 2 + d 1 ^ 2 := Real.sq_sqrt (by positivity)
  by_contra h
  have h' : ¬(|d 0| ≥ H / 3) ∧ ¬(|d 1| ≥ H / 3) := by
    simpa [not_or] using h
  have h1 : |d 0| < H / 3 := by
    have h11 : ¬(|d 0| ≥ H / 3) := h'.1
    exact lt_of_not_ge h11
  have h2 : |d 1| < H / 3 := by
    have h21 : ¬(|d 1| ≥ H / 3) := h'.2
    exact lt_of_not_ge h21
  have h3 : d 0 ^ 2 < (H / 3) ^ 2 := by
    have h4 : |d 0| ^ 2 < (H / 3) ^ 2 := by gcongr
    have h5 : |d 0| ^ 2 = d 0 ^ 2 := by simp [sq_abs]
    rw [h5] at h4
    exact h4
  have h6 : d 1 ^ 2 < (H / 3) ^ 2 := by
    have h7 : |d 1| ^ 2 < (H / 3) ^ 2 := by gcongr
    have h8 : |d 1| ^ 2 = d 1 ^ 2 := by simp [sq_abs]
    rw [h8] at h7
    exact h7
  have h3' : d 0 ^ 2 < H ^ 2 / 9 := by
    have h9 : (H / 3) ^ 2 = H ^ 2 / 9 := by ring
    rw [h9] at h3
    exact h3
  have h6' : d 1 ^ 2 < H ^ 2 / 9 := by
    have h10 : (H / 3) ^ 2 = H ^ 2 / 9 := by ring
    rw [h10] at h6
    exact h6
  nlinarith

/-- The horizontal perpendicular has `|v 0| ≥ 1/3` when `|d 1| ≥ H/3`. -/
lemma horizontalPerpendicular_v0_bound (d : Point3) (h : d 0 ≠ 0 ∨ d 1 ≠ 0)
    (h1 : |d 1| ≥ Real.sqrt (d 0 ^ 2 + d 1 ^ 2) / 3) :
    |(horizontalPerpendicular d h) 0| ≥ 1 / 3 := by
  let H := Real.sqrt (d 0 ^ 2 + d 1 ^ 2)
  have hH_pos : 0 < H := by
    have h2 : 0 < d 0 ^ 2 + d 1 ^ 2 := by
      cases h with
      | inl h0 => exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (by positivity)
      | inr h1 => exact add_pos_of_nonneg_of_pos (by positivity) (sq_pos_of_ne_zero h1)
    exact Real.sqrt_pos.mpr h2
  have hv0 : (horizontalPerpendicular d h) 0 = -d 1 / H := by
    have h_eq : horizontalPerpendicular d h = point3 (-d 1 / H) (d 0 / H) 0 := by
      simp [horizontalPerpendicular, point3] <;> rfl
    rw [h_eq] <;> simp [point3]
  rw [hv0]
  have h3 : |(-d 1 / H)| = |d 1| / H := by
    rw [abs_div, abs_neg]
    <;> rw [abs_of_pos hH_pos]
    <;> ring
  rw [h3]
  have h4 : |d 1| / H ≥ 1 / 3 := by
    calc |d 1| / H
      ≥ (H / 3) / H := by gcongr
    _ = 1 / 3 := by
      field_simp [hH_pos.ne'] <;> ring
  exact h4

/-- Swap x and y coordinates of a Point3. -/
def swapXY (p : Point3) : Point3 :=
  point3 (p 1) (p 0) (p 2)

/-- For any direction with nonzero horizontal component, either:
  - the original horizontal perpendicular has |v0| ≥ 1/3, or
  - after swapping x and y, the new horizontal perpendicular has |v0| ≥ 1/3.

This follows from `horizontal_component_bound`: at least one of |d0|, |d1| ≥ H/3.
If |d1| ≥ H/3, the original v works. If |d0| ≥ H/3, the swapped d' has |d'1| = |d0| ≥ H/3. -/
lemma horizontalPerpendicular_axis_swap (d : Point3) (h : d 0 ≠ 0 ∨ d 1 ≠ 0) :
    (|(horizontalPerpendicular d h) 0| ≥ 1 / 3) ∨
    (let d' := swapXY d
     let h' : d' 0 ≠ 0 ∨ d' 1 ≠ 0 := by
       have h1 : d' 0 = d 1 := by simp [d', swapXY, point3]
       have h2 : d' 1 = d 0 := by simp [d', swapXY, point3]
       rw [h1, h2]; exact h.symm
     |(horizontalPerpendicular d' h') 0| ≥ 1 / 3) := by
  have hH : 0 < d 0 ^ 2 + d 1 ^ 2 := by
    cases h with
    | inl h0 => exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h0) (by positivity)
    | inr h1 => exact add_pos_of_nonneg_of_pos (by positivity) (sq_pos_of_ne_zero h1)
  have h_bound := horizontal_component_bound d hH
  cases h_bound with
  | inl h_d0 =>
    -- |d0| ≥ H/3: swap case
    right
    let d' := swapXY d
    have h' : d' 0 ≠ 0 ∨ d' 1 ≠ 0 := by
      have h1 : d' 0 = d 1 := by simp [d', swapXY, point3]
      have h2 : d' 1 = d 0 := by simp [d', swapXY, point3]
      rw [h1, h2]; exact h.symm
    have h_d'1 : |d' 1| ≥ Real.sqrt (d' 0 ^ 2 + d' 1 ^ 2) / 3 := by
      have h3 : d' 0 = d 1 := by simp [d', swapXY, point3]
      have h4 : d' 1 = d 0 := by simp [d', swapXY, point3]
      have h5 : d' 0 ^ 2 + d' 1 ^ 2 = d 0 ^ 2 + d 1 ^ 2 := by
        rw [h3, h4] <;> ring
      have h6 : |d' 1| = |d 0| := by rw [h4]
      have h7 : Real.sqrt (d' 0 ^ 2 + d' 1 ^ 2) = Real.sqrt (d 0 ^ 2 + d 1 ^ 2) := by
        rw [h5]
      rw [h6, h7]
      exact h_d0
    exact horizontalPerpendicular_v0_bound d' h' h_d'1
  | inr h_d1 =>
    -- |d1| ≥ H/3: original case
    left
    exact horizontalPerpendicular_v0_bound d h h_d1

/-- Any point in the horizontal slice of a paper tube is within `21*δ` of the
axis crossing point at height `z`.

Given a line-class tube (`|direction 2| ≥ 1/2`), for any `p` in the `6δ`-tube
at height `z`, let `q_z` be the point on the axis line at height `z`. Then
`dist(p, q_z) ≤ 21*δ`. -/
lemma tube_slice_point_within_21δ
    {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ)
    (hdir : 1 / 2 ≤ |T.direction (2 : Fin 3)|)
    (z : ℝ)
    (p : Point3)
    (hp_in_tube : p ∈ wz1PaperTubeCarrier T)
    (hp_height : p (2 : Fin 3) = z) :
    let t_z : ℝ := (z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3)
    let q_z : Point3 := T.base + t_z • T.direction
    dist p q_z ≤ 21 * δ := by
  have hdir2_ne_zero : T.direction (2 : Fin 3) ≠ 0 := by
    intro h
    rw [h] at hdir
    norm_num at hdir <;> linarith
  let t_z : ℝ := (z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3)
  let q_z : Point3 := T.base + t_z • T.direction
  have h_edist : Metric.infEDist p (tubeAxisLine T) ≤ ENNReal.ofReal (6 * δ) := by
    have h : p ∈ Metric.cthickening (6 * δ) (tubeAxisLine T) := hp_in_tube.1
    have h' := Metric.cthickening_eq_preimage_infEDist (6 * δ) (tubeAxisLine T)
    rw [h'] at h
    exact h
  have h7 : Metric.infEDist p (tubeAxisLine T) < ENNReal.ofReal (7 * δ) := by
    have h8 : (6 * δ : ℝ) < (7 * δ : ℝ) := by linarith
    have h12 : ENNReal.ofReal (6 * δ) < ENNReal.ofReal (7 * δ) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)] <;> linarith
    exact h_edist.trans_lt h12
  rcases tube_axis_exists_point T p (by linarith) h7 with ⟨q, hq_line, hdist_lt⟩
  have hdist : dist p q < 7 * δ := hdist_lt
  have hnorm : ‖p - q‖ < 7 * δ := by simpa [dist_eq_norm] using hdist
  rcases hq_line with ⟨t, rfl⟩
  set qt : Point3 := T.base + t • T.direction with hqt_def
  have h1 : ‖p - qt‖ < 7 * δ := hnorm
  have h3 : |(p - qt) (2 : Fin 3)| ≤ ‖p - qt‖ := PiLp.norm_apply_le (p - qt) (2 : Fin 3)
  have h5 : |qt (2 : Fin 3) - z| ≤ 7 * δ := by
    have h6 : |p (2 : Fin 3) - qt (2 : Fin 3)| < 7 * δ := h3.trans_lt h1
    rw [hp_height] at h6
    have h7 : |z - qt (2 : Fin 3)| < 7 * δ := h6
    have h8 : |qt (2 : Fin 3) - z| = |z - qt (2 : Fin 3)| := by rw [abs_sub_comm]
    rw [h8]; exact h7.le
  have h7 : |t - t_z| ≤ 14 * δ := by
    have h8 : t - t_z = (qt (2 : Fin 3) - z) / T.direction (2 : Fin 3) := by
      dsimp only [t_z]
      have h9 : qt (2 : Fin 3) = T.base (2 : Fin 3) + t * T.direction (2 : Fin 3) := by
        simp [qt, Pi.add_apply, Pi.smul_apply] <;> ring
      rw [h9]
      field_simp [hdir2_ne_zero] <;> ring
    rw [h8]
    have h9 : |(qt (2 : Fin 3) - z) / T.direction (2 : Fin 3)| =
        |qt (2 : Fin 3) - z| / |T.direction (2 : Fin 3)| := by rw [abs_div]
    rw [h9]
    have h10 : |T.direction (2 : Fin 3)| ≥ 1 / 2 := hdir
    calc |qt (2 : Fin 3) - z| / |T.direction (2 : Fin 3)|
      ≤ (7 * δ) / (1 / 2 : ℝ) := by gcongr
    _ = 14 * δ := by ring
  have h_dist_q_qz : dist qt q_z ≤ 14 * δ := by
    have h : dist qt q_z = ‖qt - q_z‖ := by rfl
    rw [h]
    have h_comp : ∀ (i : Fin 3), (qt - q_z) i = (t - t_z) * T.direction i := by
      intro i
      fin_cases i <;> simp [qt, q_z] <;> ring
    have h2 : qt - q_z = (t - t_z) • T.direction := by
      exact PiLp.ext h_comp
    rw [h2]
    rw [norm_smul]
    have h3 : ‖T.direction‖ = 1 := T.direction_unit
    rw [h3]
    <;> simpa using h7
  have h_main : dist p q_z ≤ 21 * δ := by
    calc dist p q_z
      ≤ dist p qt + dist qt q_z := dist_triangle p qt q_z
    _ ≤ (7 * δ) + (14 * δ) := by linarith [h1, h_dist_q_qz]
    _ = 21 * δ := by ring
  exact h_main

/-- The horizontal slice of a paper tube has diameter at most `42*δ`.

For any two points `p1, p2` in the horizontal slice at height `z`,
`dist(p1, p2) ≤ 42*δ`. -/
lemma tube_slice_diameter_bound
    {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ)
    (hdir : 1 / 2 ≤ |T.direction (2 : Fin 3)|)
    (z : ℝ) :
    ∀ (p1 p2 : Point3),
      p1 ∈ horizontalSlice (wz1PaperTubeCarrier T) z →
      p2 ∈ horizontalSlice (wz1PaperTubeCarrier T) z →
      dist p1 p2 ≤ 42 * δ := by
  intro p1 p2 hp1 hp2
  have h1 := tube_slice_point_within_21δ hδ T hdir z p1 hp1.1 hp1.2
  have h2 := tube_slice_point_within_21δ hδ T hdir z p2 hp2.1 hp2.2
  let t_z : ℝ := (z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3)
  let q_z : Point3 := T.base + t_z • T.direction
  have h3 : dist p1 q_z ≤ 21 * δ := h1
  have h4 : dist p2 q_z ≤ 21 * δ := h2
  have h5 : dist q_z p2 = dist p2 q_z := dist_comm _ _
  calc dist p1 p2
    ≤ dist p1 q_z + dist q_z p2 := dist_triangle p1 q_z p2
  _ = dist p1 q_z + dist p2 q_z := by rw [h5]
  _ ≤ (21 * δ) + (21 * δ) := by linarith
  _ = 42 * δ := by ring

/-- If the horizontal slice is nonempty, it is contained in a ball of radius
`42*δ` around any point in the slice.

For `δ ≤ 1/1764`, we have `42*δ ≤ √δ`, so the slice fits in a ball of radius `√δ`. -/
lemma tube_slice_contained_in_ball
    {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ)
    (hdir : 1 / 2 ≤ |T.direction (2 : Fin 3)|)
    (z : ℝ)
    (p0 : Point3)
    (hp0 : p0 ∈ horizontalSlice (wz1PaperTubeCarrier T) z) :
    horizontalSlice (wz1PaperTubeCarrier T) z ⊆ Metric.closedBall p0 (42 * δ) := by
  intro p hp
  exact tube_slice_diameter_bound hδ T hdir z p p0 hp hp0

/-- A sufficiently vertical line-class tube has axis points at every height in [-1,1]
within the cropped box `[-1,1]^3`.

If `wz1PaperDirection tube (2) ≥ 3/√13`, then for every `z ∈ [-1,1]`, the axis
point at height `z` satisfies `|x| ≤ 1` and `|y| ≤ 1`, hence lies in `axisBox 2 2 2`
and therefore in `wz1PaperTubeCarrier tube`.

The threshold `3/√13 ≈ 0.832` comes from requiring both transverse components
to satisfy `|d_i| / d_z ≤ 2/3`, so that `1/3 + 2/3 = 1`. -/
lemma vertical_tube_spans_full_height
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    (h_vertical : (3 : ℝ) / Real.sqrt 13 ≤ wz1PaperDirection tube (2 : Fin 3)) :
    ∀ (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 →
      wz1PaperAxisPointAtHeight tube z ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
  let d := wz1PaperDirection tube
  let z0 := wz1TubeAxisZeroPoint tube
  have hd_unit : ‖d‖ = 1 := wz1PaperDirection_norm tube
  have hdz_pos : 0 < d (2 : Fin 3) := by
    have h : (1 / 2 : ℝ) ≤ d (2 : Fin 3) := hline.1
    linarith
  have hdz2 : d (2 : Fin 3) ^ 2 ≥ 9 / 13 := by
    have hpos : 0 ≤ d (2 : Fin 3) := by linarith
    have h : (d (2 : Fin 3)) ^ 2 ≥ ((3 : ℝ) / Real.sqrt 13) ^ 2 := by gcongr
    have h2 : ((3 : ℝ) / Real.sqrt 13) ^ 2 = 9 / 13 := by
      rw [div_pow]
      have h3 : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
      rw [h3] <;> norm_num
    linarith
  have hz0_2 : z0 (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube hline.vertical
  have hz0_0 : |z0 (0 : Fin 3)| ≤ 1 / 3 := hline.2.1
  have hz0_1 : |z0 (1 : Fin 3)| ≤ 1 / 3 := hline.2.2
  have h_norm_sq : d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 = 1 := by
    have h : ‖d‖ ^ 2 = d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ] <;> ring
    rw [hd_unit] at h
    norm_num at h ⊢ <;> linarith
  have hd0_bound : |d 0| / d 2 ≤ 2 / 3 := by
    have h1 : d 0 ^ 2 ≤ 4 / 13 := by nlinarith
    have h2 : d 0 ^ 2 ≤ (4 / 9 : ℝ) * d 2 ^ 2 := by nlinarith
    have h3 : |d 0| ≤ (2 / 3 : ℝ) * d 2 := by
      nlinarith [abs_nonneg (d 0), abs_nonneg (d 2), sq_abs (d 0), sq_abs (d 2)]
    have h4 : 0 < d 2 := hdz_pos
    calc |d 0| / d 2 ≤ ((2 / 3 : ℝ) * d 2) / d 2 := by gcongr
      _ = 2 / 3 := by field_simp [h4.ne'] <;> ring
  have hd1_bound : |d 1| / d 2 ≤ 2 / 3 := by
    have h1 : d 1 ^ 2 ≤ 4 / 13 := by nlinarith
    have h2 : d 1 ^ 2 ≤ (4 / 9 : ℝ) * d 2 ^ 2 := by nlinarith
    have h3 : |d 1| ≤ (2 / 3 : ℝ) * d 2 := by
      nlinarith [abs_nonneg (d 1), abs_nonneg (d 2), sq_abs (d 1), sq_abs (d 2)]
    have h4 : 0 < d 2 := hdz_pos
    calc |d 1| / d 2 ≤ ((2 / 3 : ℝ) * d 2) / d 2 := by gcongr
      _ = 2 / 3 := by field_simp [h4.ne'] <;> ring
  intro z hz
  have hz1 : -1 ≤ z := hz.1
  have hz2 : z ≤ 1 := hz.2
  have h_abs_z : |z| ≤ 1 := by
    rw [abs_le]
    exact ⟨hz1, hz2⟩
  let p := wz1PaperAxisPointAtHeight tube z
  have hp2 : p 2 = z := wz1PaperAxisPointAtHeight_coord_two hline z
  have hp0 : p 0 = z0 0 + z * d 0 / d 2 := by
    simp [p, wz1PaperAxisPointAtHeight, z0] <;> ring
  have hp1 : p 1 = z0 1 + z * d 1 / d 2 := by
    simp [p, wz1PaperAxisPointAtHeight, z0] <;> ring
  have h_p0_abs : |p 0| ≤ 1 := by
    rw [hp0]
    calc |z0 0 + z * d 0 / d 2|
      ≤ |z0 0| + |z * d 0 / d 2| := by exact abs_add_le _ _
    _ = |z0 0| + |z| * (|d 0| / d 2) := by
      have h5 : |z * d 0 / d 2| = |z| * (|d 0| / d 2) := by
        have h6 : |d 2| = d 2 := abs_of_pos hdz_pos
        simp [abs_div, abs_mul, h6] <;> ring
      rw [h5]
    _ ≤ 1 / 3 + 1 * (2 / 3 : ℝ) := by gcongr <;> linarith
    _ = 1 := by norm_num
  have h_p1_abs : |p 1| ≤ 1 := by
    rw [hp1]
    calc |z0 1 + z * d 1 / d 2|
      ≤ |z0 1| + |z * d 1 / d 2| := by exact abs_add_le _ _
    _ = |z0 1| + |z| * (|d 1| / d 2) := by
      have h5 : |z * d 1 / d 2| = |z| * (|d 1| / d 2) := by
        have h6 : |d 2| = d 2 := abs_of_pos hdz_pos
        simp [abs_div, abs_mul, h6] <;> ring
      rw [h5]
    _ ≤ 1 / 3 + 1 * (2 / 3 : ℝ) := by gcongr <;> linarith
    _ = 1 := by norm_num
  have h_p2_abs : |p 2| ≤ 1 := by
    rw [hp2]
    exact h_abs_z
  simpa [Kakeya.Streamlined.axisBox] using ⟨h_p0_abs, h_p1_abs, h_p2_abs⟩

/-- For a sufficiently vertical line-class tube, the axis point at every height
in [-1,1] lies in the paper tube carrier. -/
lemma vertical_tube_axis_point_in_carrier
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    (h_vertical : (3 : ℝ) / Real.sqrt 13 ≤ wz1PaperDirection tube (2 : Fin 3))
    (hdelta_pos : 0 < delta) :
    ∀ (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 →
      wz1PaperAxisPointAtHeight tube z ∈ wz1PaperTubeCarrier tube := by
  intro z hz
  have h_in_box : wz1PaperAxisPointAtHeight tube z ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    vertical_tube_spans_full_height hline h_vertical z hz
  have h_on_axis : wz1PaperAxisPointAtHeight tube z ∈ tubeAxisLine tube :=
    wz1PaperAxisPointAtHeight_mem_axis tube z
  have h_in_thickening : wz1PaperAxisPointAtHeight tube z ∈
      Metric.cthickening (6 * delta) (tubeAxisLine tube) :=
    Metric.self_subset_cthickening (tubeAxisLine tube) h_on_axis
  exact ⟨h_in_thickening, h_in_box⟩

end Kakeya.Assouad
