import MyLeanRepo.Kakeya.CV.Isoperimetric.Statements
import MyLeanRepo.Kakeya.CV.Isoperimetric.SphereProjection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod


open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace Kakeya.CV

noncomputable section

-- ======================================================================
-- Reflection: linear isometry mapping any unit vector to any other
-- ======================================================================

/-- Given unit vectors x, y in Point 3, there exists a linear isometry f with f x = y.
    Uses reflection across the hyperplane perpendicular to x - y. -/
lemma exists_linear_isometry_map (x y : Point 3)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ (f : Point 3 →ₗᵢ[ℝ] Point 3), f x = y := by
  by_cases hxy : x = y
  · refine ⟨LinearIsometry.id, ?_⟩
    exact congr_arg id hxy
  · let v : Point 3 := x - y
    have hv_ne_zero : v ≠ 0 := by
      intro h
      have h' : x - y = 0 := h
      have : x = y := sub_eq_zero.mp h'
      exact hxy this
    have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne_zero
    have h_norm2_pos : 0 < ‖v‖ ^ 2 := by positivity
    let c : ℝ := 2 / ‖v‖ ^ 2
    let f_lm : Point 3 →ₗ[ℝ] Point 3 :=
      { toFun := fun z => z - (c * inner ℝ z v) • v
        map_add' := by
          intro z w
          have h : inner ℝ (z + w) v = inner ℝ z v + inner ℝ w v := by
            exact inner_add_left z w v
          rw [h]
          have h2 : (c * (inner ℝ z v + inner ℝ w v)) • v =
              (c * inner ℝ z v) • v + (c * inner ℝ w v) • v := by
            have h21 : c * (inner ℝ z v + inner ℝ w v) = c * inner ℝ z v + c * inner ℝ w v := by ring
            rw [h21, add_smul]
          rw [h2]
          have h3 : ∀ (a b d e : Point 3), (a + b) - (d + e) = (a - d) + (b - e) := by
            intro a b d e; simp [sub_eq_add_neg, add_assoc] <;> abel
          exact h3 z w ((c * inner ℝ z v) • v) ((c * inner ℝ w v) • v)
        map_smul' := by
          intro a z
          have h : inner ℝ (a • z) v = a * inner ℝ z v := by
            simp [inner_smul_left] <;> ring
          have h_goal : a • z - (c * inner ℝ (a • z) v) • v = a • (z - (c * inner ℝ z v) • v) := by
            rw [h]
            have h1 : a • (z - (c * inner ℝ z v) • v) = a • z - a • ((c * inner ℝ z v) • v) := by rw [smul_sub]
            rw [h1]
            have h2 : a • ((c * inner ℝ z v) • v) = (a * (c * inner ℝ z v)) • v := by
              exact smul_smul a (c * inner ℝ z v) v
            rw [h2]
            have h3 : c * (a * inner ℝ z v) = a * (c * inner ℝ z v) := by ring
            rw [h3]
          simpa using h_goal }
    let f : Point 3 → Point 3 := f_lm
    have hf_def : ∀ z, f z = z - (c * inner ℝ z v) • v := by intro z; rfl
    have h_c2 : c * ‖v‖ ^ 2 = 2 := by
      simp [c, h_norm2_pos.ne'] <;> field_simp [h_norm2_pos.ne'] <;> ring
    have h_inner : ∀ (z w : Point 3), inner ℝ (f z) (f w) = inner ℝ z w := by
      intro z w
      set izv : ℝ := inner ℝ z v with hizv_def
      set iwv : ℝ := inner ℝ w v with hiwv_def
      have h_expand : inner ℝ (f z) (f w) =
          inner ℝ z w - c * izv * iwv - c * iwv * izv + c * izv * (c * iwv) * inner ℝ v v := by
        rw [hf_def z, hf_def w]
        have h1 : inner ℝ (z - (c * izv) • v) (w - (c * iwv) • v) =
            inner ℝ z w - (c * iwv) * inner ℝ z v - (c * izv) * inner ℝ v w + (c * izv) * (c * iwv) * inner ℝ v v := by
          have h11 : inner ℝ (z - (c * izv) • v) (w - (c * iwv) • v) =
              inner ℝ z (w - (c * iwv) • v) - inner ℝ ((c * izv) • v) (w - (c * iwv) • v) := by
            exact inner_sub_left z ((c * izv) • v) (w - (c * iwv) • v)
          rw [h11]
          have h12 : inner ℝ z (w - (c * iwv) • v) = inner ℝ z w - (c * iwv) * inner ℝ z v := by
            have h121 : inner ℝ z (w - (c * iwv) • v) = inner ℝ z w - inner ℝ z ((c * iwv) • v) := by
              exact inner_sub_right z w ((c * iwv) • v)
            rw [h121]
            have h122 : inner ℝ z ((c * iwv) • v) = (c * iwv) * inner ℝ z v := by
              simp [inner_smul_right] <;> ring
            rw [h122] <;> ring
          have h13 : inner ℝ ((c * izv) • v) (w - (c * iwv) • v) =
              (c * izv) * inner ℝ v w - (c * izv) * (c * iwv) * inner ℝ v v := by
            have h131 : inner ℝ ((c * izv) • v) (w - (c * iwv) • v) =
                inner ℝ ((c * izv) • v) w - inner ℝ ((c * izv) • v) ((c * iwv) • v) := by
              exact inner_sub_right ((c * izv) • v) w ((c * iwv) • v)
            rw [h131]
            have h132 : inner ℝ ((c * izv) • v) w = (c * izv) * inner ℝ v w := by
              simp [inner_smul_left] <;> ring
            have h133 : inner ℝ ((c * izv) • v) ((c * iwv) • v) = (c * izv) * (c * iwv) * inner ℝ v v := by
              simp [inner_smul_left, inner_smul_right] <;> ring
            rw [h132, h133] <;> ring
          rw [h12, h13] <;> abel
        rw [h1]
        have h21 : inner ℝ z v = izv := hizv_def.symm
        have h22 : inner ℝ v w = inner ℝ w v := (real_inner_comm v w).symm
        have h23 : inner ℝ w v = iwv := hiwv_def.symm
        rw [h21, h22, h23] <;> ring
      rw [h_expand]
      have hvv : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [hvv]
      have h_goal : inner ℝ z w - c * izv * iwv - c * iwv * izv + c * izv * (c * iwv) * ‖v‖ ^ 2 = inner ℝ z w := by
        have h : c * izv * (c * iwv) * ‖v‖ ^ 2 = 2 * c * izv * iwv := by
          calc
            c * izv * (c * iwv) * ‖v‖ ^ 2 = c^2 * izv * iwv * ‖v‖ ^ 2 := by ring
            _ = c * (c * ‖v‖ ^ 2) * izv * iwv := by ring
            _ = c * 2 * izv * iwv := by rw [h_c2] <;> ring
            _ = 2 * c * izv * iwv := by ring
        rw [h] <;> ring
      exact h_goal
    have h_norm : ∀ z, ‖f z‖ = ‖z‖ := by
      intro z
      have h5 : ‖f z‖ ^ 2 = inner ℝ (f z) (f z) := by
        simpa using real_inner_self_eq_norm_sq (f z)
      have h6 : ‖z‖ ^ 2 = inner ℝ z z := by
        simpa using real_inner_self_eq_norm_sq z
      have h7 : ‖f z‖ ^ 2 = ‖z‖ ^ 2 := by rw [h5, h6, h_inner z z]
      have h8 : 0 ≤ ‖f z‖ := by positivity
      have h9 : 0 ≤ ‖z‖ := by positivity
      nlinarith
    let f_li : Point 3 →ₗᵢ[ℝ] Point 3 :=
      { toLinearMap := f_lm
        norm_map' := h_norm }
    have h_inner_xv : inner ℝ x v = ‖v‖ ^ 2 / 2 := by
      have h_vdef : v = x - y := by rfl
      have h1 : inner ℝ x v = inner ℝ x x - inner ℝ x y := by
        rw [h_vdef]; simp [inner_sub_right] <;> ring
      have h2 : ‖v‖ ^ 2 = inner ℝ x x + inner ℝ y y - 2 * inner ℝ x y := by
        rw [h_vdef]
        have h3 : ‖x - y‖ ^ 2 = inner ℝ (x - y) (x - y) := by
          exact Eq.symm (real_inner_self_eq_norm_sq (x - y))
        rw [h3]
        have h4 : inner ℝ (x - y) (x - y) = inner ℝ x x - inner ℝ x y - inner ℝ y x + inner ℝ y y := by
          have h41 : inner ℝ (x - y) (x - y) = inner ℝ x (x - y) - inner ℝ y (x - y) := by
            exact inner_sub_left x y (x - y)
          rw [h41]
          have h42 : inner ℝ x (x - y) = inner ℝ x x - inner ℝ x y := by
            exact inner_sub_right x x y
          have h43 : inner ℝ y (x - y) = inner ℝ y x - inner ℝ y y := by
            exact inner_sub_right y x y
          rw [h42, h43] <;> abel
        rw [h4]
        have h5 : inner ℝ y x = inner ℝ x y := (real_inner_comm y x).symm
        rw [h5] <;> ring
      have hxx : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
      have hyy : inner ℝ y y = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
      rw [h1, h2, hxx, hyy, hx, hy] <;> ring
    have hfx : f x = y := by
      rw [hf_def x, h_inner_xv]
      have h4 : c * (‖v‖ ^ 2 / 2) = 1 := by
        simp [c, h_norm2_pos.ne'] <;> field_simp [h_norm2_pos.ne'] <;> ring
      rw [h4]
      have h5 : x - (1 : ℝ) • v = y := by
        have h6 : (1 : ℝ) • v = v := by simp
        rw [h6]
        <;> simp [v, sub_eq_add_neg] <;> abel
      exact h5
    exact ⟨f_li, hfx⟩

-- ======================================================================
-- North pole and caps
-- ======================================================================

/-- The north pole of the unit sphere. -/
def northPole : Point 3 := mkPoint3 ![1, 0, 0]

lemma northPole_sphere : northPole ∈ unitSphere 3 := by
  have h1 : (northPole 0)^2 + (northPole 1)^2 + (northPole 2)^2 = 1 := by
    simp [northPole, mkPoint3_apply] <;> norm_num
  have h2 : ‖northPole‖ ^ 2 = (northPole 0)^2 + (northPole 1)^2 + (northPole 2)^2 :=
    norm_sq_point3 northPole
  have h3 : ‖northPole‖ ^ 2 = 1 := by linarith
  have h4 : 0 ≤ ‖northPole‖ := by positivity
  have h5 : ‖northPole‖ = 1 := by nlinarith
  simpa [unitSphere, Metric.mem_sphere] using h5

/-- A spherical cap of chordal radius `r` centered at point `x` on the unit sphere. -/
def sphereCap (x : Point 3) (r : ℝ) : Set (Point 3) :=
  unitSphere 3 ∩ closedBall x r

-- ======================================================================
-- Radius independence via isometry
-- ======================================================================

/-- μHE[2] of a cap depends only on its radius. -/
lemma muHE_two_cap_radius_independent (x y : Point 3)
    (hx : x ∈ unitSphere 3) (hy : y ∈ unitSphere 3) (r : ℝ) :
    (μHE[2] : Measure (Point 3)) (sphereCap x r) =
    (μHE[2] : Measure (Point 3)) (sphereCap y r) := by
  have hx1 : ‖x‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hx
  have hy1 : ‖y‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hy
  rcases exists_linear_isometry_map x y hx1 hy1 with ⟨f, hfx⟩
  rcases exists_linear_isometry_map y x hy1 hx1 with ⟨g, hgx⟩
  have h_sphere_f : ∀ z, z ∈ unitSphere 3 → f z ∈ unitSphere 3 := by
    intro z hz
    have h1 : ‖z‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hz
    have h3 : ‖f z‖ = 1 := by rw [f.norm_map z, h1]
    simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h3
  have h_sphere_g : ∀ z, z ∈ unitSphere 3 → g z ∈ unitSphere 3 := by
    intro z hz
    have h1 : ‖z‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hz
    have h3 : ‖g z‖ = 1 := by rw [g.norm_map z, h1]
    simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h3
  have h1 : f '' sphereCap x r ⊆ sphereCap y r := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    have h4 : f z ∈ unitSphere 3 := h_sphere_f z hz.1
    have h5 : dist (f z) y ≤ r := by
      have h6 : dist (f z) y = dist (f z) (f x) := by rw [hfx]
      rw [h6]
      exact f.isometry.dist_eq z x ▸ hz.2
    exact ⟨h4, h5⟩
  have h2 : g '' sphereCap y r ⊆ sphereCap x r := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    have h4 : g z ∈ unitSphere 3 := h_sphere_g z hz.1
    have h5 : dist (g z) x ≤ r := by
      have h6 : dist (g z) x = dist (g z) (g y) := by rw [hgx]
      rw [h6]
      exact g.isometry.dist_eq z y ▸ hz.2
    exact ⟨h4, h5⟩
  have h_eq1 : (μHE[2] : Measure (Point 3)) (f '' sphereCap x r) =
      (μHE[2] : Measure (Point 3)) (sphereCap x r) :=
    f.isometry.euclideanHausdorffMeasure_image (sphereCap x r)
  have h_eq2 : (μHE[2] : Measure (Point 3)) (g '' sphereCap y r) =
      (μHE[2] : Measure (Point 3)) (sphereCap y r) :=
    g.isometry.euclideanHausdorffMeasure_image (sphereCap y r)
  have h_le1 : (μHE[2] : Measure (Point 3)) (sphereCap x r) ≤
      (μHE[2] : Measure (Point 3)) (sphereCap y r) := by
    rw [← h_eq1]
    exact measure_mono h1
  have h_le2 : (μHE[2] : Measure (Point 3)) (sphereCap y r) ≤
      (μHE[2] : Measure (Point 3)) (sphereCap x r) := by
    rw [← h_eq2]
    exact measure_mono h2
  exact le_antisymm h_le1 h_le2

-- ======================================================================
-- graphMap Lipschitz and measure transfer
-- ======================================================================

/-- The north-hemisphere graph map from Point 2 to Point 3:
`(y,z) ↦ (√(1-y²-z²), y, z)`. -/
def northSphereGraphMap (q : Point 2) : Point 3 :=
  mkPoint3 (fun i : Fin 3 =>
    if i = 0 then Real.sqrt (1 - (q 0)^2 - (q 1)^2)
    else if i = 1 then q 0
    else q 1)

local notation "graphMap" => northSphereGraphMap

/-- Algebraic helper: (a+b)^2 + (c+d)^2 ≤ 2*(a^2+c^2) + 2*(b^2+d^2). -/
lemma sum_sq_bound_helper (y1 z1 y2 z2 : ℝ) :
    (y1 + y2)^2 + (z1 + z2)^2 ≤ 2 * (y1^2 + z1^2) + 2 * (y2^2 + z2^2) := by
  have h1 : (y1 + y2)^2 ≤ 2 * (y1^2 + y2^2) := by
    have h : (y1 - y2)^2 ≥ 0 := by positivity
    linarith
  have h2 : (z1 + z2)^2 ≤ 2 * (z1^2 + z2^2) := by
    have h : (z1 - z2)^2 ≥ 0 := by positivity
    linarith
  linarith

/-- Cauchy-Schwarz in 2D. -/
lemma cauchy_schwarz_2d (a b c d : ℝ) :
    (a * c + b * d)^2 ≤ (a^2 + b^2) * (c^2 + d^2) := by
  have h : (a * d - b * c)^2 ≥ 0 := by positivity
  nlinarith

/-- Component accessors for graphMap. -/
lemma graphMap_apply0 (q : Point 2) :
    graphMap q 0 = Real.sqrt (1 - (q 0)^2 - (q 1)^2) := by
  unfold northSphereGraphMap
  rw [mkPoint3_apply]
  <;> simp

lemma graphMap_apply1 (q : Point 2) : graphMap q 1 = q 0 := by
  unfold northSphereGraphMap
  rw [mkPoint3_apply]
  <;> simp

lemma graphMap_apply2 (q : Point 2) : graphMap q 2 = q 1 := by
  unfold northSphereGraphMap
  rw [mkPoint3_apply]
  <;> simp

/-- Norm squared in Point 2. -/
lemma norm_sq_point2 (p : Point 2) : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 := by
  have h : ‖p‖ ^ 2 = ∑ i : Fin 2, (p i)^2 := EuclideanSpace.real_norm_sq_eq p
  rw [h, Fin.sum_univ_two] <;> ring

/-- Core algebraic bound for graphMap Lipschitz constant. -/
lemma graphMap_lipschitz_core (y1 z1 y2 z2 ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hs1_le : y1^2 + z1^2 ≤ ρ^2)
    (hs2_le : y2^2 + z2^2 ≤ ρ^2) :
    let s1 := y1^2 + z1^2
    let s2 := y2^2 + z2^2
    let d2 := (y1 - y2)^2 + (z1 - z2)^2
    let r1 := Real.sqrt (1 - s1)
    let r2 := Real.sqrt (1 - s2)
    (r1 - r2)^2 + d2 ≤ (1 / (1 - ρ^2)) * d2 := by
  set s1 := y1^2 + z1^2 with hs1
  set s2 := y2^2 + z2^2 with hs2
  set d2 := (y1 - y2)^2 + (z1 - z2)^2 with hd2
  set r1 := Real.sqrt (1 - s1) with hr1
  set r2 := Real.sqrt (1 - s2) with hr2
  have h_pos : 0 < 1 - ρ^2 := by nlinarith
  have h1s1 : 0 ≤ 1 - s1 := by nlinarith
  have h1s2 : 0 ≤ 1 - s2 := by nlinarith
  have h1s1_pos : 0 < 1 - s1 := by nlinarith
  have h1s2_pos : 0 < 1 - s2 := by nlinarith
  have h_r1_pos : 0 < r1 := Real.sqrt_pos.mpr h1s1_pos
  have h_r2_pos : 0 < r2 := Real.sqrt_pos.mpr h1s2_pos
  have h_r1r2_pos : 0 < r1 + r2 := by linarith
  set a := y1 - y2 with ha
  set b := z1 - z2 with hb
  set c := y1 + y2 with hc
  set d := z1 + z2 with hd
  have h_cs : (s1 - s2)^2 ≤ 4 * ρ^2 * d2 := by
    have h_expand : s1 - s2 = a * c + b * d := by
      simp [ha, hb, hc, hd, hs1, hs2] <;> ring
    have h_cs2 : (a * c + b * d)^2 ≤ (a^2 + b^2) * (c^2 + d^2) := cauchy_schwarz_2d a b c d
    have h_ab : a^2 + b^2 = d2 := by simp [ha, hb, hd2] <;> ring
    have h_cd : c^2 + d^2 ≤ 4 * ρ^2 := by
      have h_bound : c^2 + d^2 ≤ 2 * s1 + 2 * s2 := sum_sq_bound_helper y1 z1 y2 z2
      have h_total : 2 * s1 + 2 * s2 ≤ 4 * ρ^2 := by linarith [hs1_le, hs2_le]
      linarith
    calc
      (s1 - s2)^2 = (a * c + b * d)^2 := by rw [h_expand]
      _ ≤ (a^2 + b^2) * (c^2 + d^2) := h_cs2
      _ = d2 * (c^2 + d^2) := by rw [h_ab] <;> ring
      _ ≤ d2 * (4 * ρ^2) := by gcongr
      _ = 4 * ρ^2 * d2 := by ring
  have h_sqrt_sq : (Real.sqrt (1 - ρ^2))^2 = 1 - ρ^2 := Real.sq_sqrt (by nlinarith)
  have h_ge1 : r1 ≥ Real.sqrt (1 - ρ^2) := by
    rw [hr1]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h_ge2 : r2 ≥ Real.sqrt (1 - ρ^2) := by
    rw [hr2]; exact Real.sqrt_le_sqrt (by nlinarith)
  have h_sum_both : r1 + r2 ≥ 2 * Real.sqrt (1 - ρ^2) := by linarith
  have h_sum_sq : (r1 + r2)^2 ≥ 4 * (1 - ρ^2) := by
    have h_nonneg2 : 0 ≤ 2 * Real.sqrt (1 - ρ^2) := by positivity
    have h4 : 0 ≤ r1 + r2 := by positivity
    have h5 : (r1 + r2)^2 ≥ (2 * Real.sqrt (1 - ρ^2))^2 := by
      nlinarith
    have h6 : (2 * Real.sqrt (1 - ρ^2))^2 = 4 * (1 - ρ^2) := by
      calc
        (2 * Real.sqrt (1 - ρ^2))^2 = 4 * (Real.sqrt (1 - ρ^2))^2 := by ring
        _ = 4 * (1 - ρ^2) := by rw [h_sqrt_sq] <;> ring
    rw [h6] at h5; exact h5
  have h_prod : (r1 - r2) * (r1 + r2) = s2 - s1 := by
    have h4 : r1^2 = 1 - s1 := by rw [hr1]; rw [Real.sq_sqrt h1s1]
    have h5 : r2^2 = 1 - s2 := by rw [hr2]; rw [Real.sq_sqrt h1s2]
    linarith
  have h6 : (r1 - r2)^2 * (r1 + r2)^2 = (s2 - s1)^2 := by
    calc
      (r1 - r2)^2 * (r1 + r2)^2 = ((r1 - r2) * (r1 + r2))^2 := by ring
      _ = (s2 - s1)^2 := by rw [h_prod]
  have h_r_diff_sq : (r1 - r2)^2 ≤ ρ^2 * d2 / (1 - ρ^2) := by
    have h7 : (r1 - r2)^2 = (s2 - s1)^2 / (r1 + r2)^2 := by
      field_simp [h_r1r2_pos.ne'] <;> linarith
    rw [h7]
    have h8 : (s2 - s1)^2 ≤ 4 * ρ^2 * d2 := by
      have h9 : (s2 - s1)^2 = (s1 - s2)^2 := by ring
      rw [h9]; exact h_cs
    have h9 : 0 < (r1 + r2)^2 := by positivity
    calc
      (s2 - s1)^2 / (r1 + r2)^2 ≤ (4 * ρ^2 * d2) / (r1 + r2)^2 := by gcongr
      _ ≤ (4 * ρ^2 * d2) / (4 * (1 - ρ^2)) := by
        gcongr <;> exact h_sum_sq
      _ = ρ^2 * d2 / (1 - ρ^2) := by
        field_simp [h_pos.ne'] <;> ring
  have h_main : (r1 - r2)^2 + d2 ≤ (1 / (1 - ρ^2)) * d2 := by
    have h9 : (r1 - r2)^2 ≤ ρ^2 * d2 / (1 - ρ^2) := h_r_diff_sq
    have h10 : (r1 - r2)^2 + d2 ≤ ρ^2 * d2 / (1 - ρ^2) + d2 := by linarith
    have h11 : ρ^2 * d2 / (1 - ρ^2) + d2 = (1 / (1 - ρ^2)) * d2 := by
      field_simp [h_pos.ne'] <;> ring
    rw [h11] at h10
    exact h10
  exact h_main

/-- graphMap is Lipschitz on disk of radius ρ with constant 1/√(1-ρ²). -/
lemma graphMap_lipschitzOnWith {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    LipschitzOnWith
      (⟨1 / Real.sqrt (1 - ρ^2), by
        have h : 0 < 1 - ρ^2 := by nlinarith
        positivity⟩ : NNReal)
      graphMap
      {q : Point 2 | (q 0)^2 + (q 1)^2 ≤ ρ^2} := by
  let C : ℝ := 1 / Real.sqrt (1 - ρ^2)
  have h_pos : 0 < 1 - ρ^2 := by nlinarith
  have hC_pos : 0 < C := by positivity
  intro q1 hq1 q2 hq2
  set y1 := q1 0 with hy1
  set z1 := q1 1 with hz1
  set y2 := q2 0 with hy2
  set z2 := q2 1 with hz2
  set s1 := y1^2 + z1^2 with hs1
  set s2 := y2^2 + z2^2 with hs2
  have hs1_le : s1 ≤ ρ^2 := hq1
  have hs2_le : s2 ≤ ρ^2 := hq2
  set r1 := Real.sqrt (1 - s1) with hr1
  set r2 := Real.sqrt (1 - s2) with hr2
  set d2 : ℝ := (y1 - y2)^2 + (z1 - z2)^2 with hd2
  have h_norm2 : ‖q1 - q2‖ ^ 2 = d2 := by
    have h : ‖q1 - q2‖ ^ 2 = ((q1 - q2) 0)^2 + ((q1 - q2) 1)^2 := norm_sq_point2 (q1 - q2)
    rw [h] <;> simp [hd2] <;> ring
  have h11 : graphMap q1 0 = r1 := by
    have h : graphMap q1 0 = Real.sqrt (1 - (q1 0)^2 - (q1 1)^2) := graphMap_apply0 q1
    rw [h]
    have h_eq : (q1 0)^2 + (q1 1)^2 = s1 := by simp [hy1, hz1, hs1] <;> ring
    have h_arg : 1 - (q1 0)^2 - (q1 1)^2 = 1 - s1 := by linarith
    rw [h_arg]
  have h12 : graphMap q2 0 = r2 := by
    have h : graphMap q2 0 = Real.sqrt (1 - (q2 0)^2 - (q2 1)^2) := graphMap_apply0 q2
    rw [h]
    have h_eq : (q2 0)^2 + (q2 1)^2 = s2 := by simp [hy2, hz2, hs2] <;> ring
    have h_arg : 1 - (q2 0)^2 - (q2 1)^2 = 1 - s2 := by linarith
    rw [h_arg]
  have h21 : graphMap q1 1 = y1 := graphMap_apply1 q1
  have h22 : graphMap q2 1 = y2 := graphMap_apply1 q2
  have h31 : graphMap q1 2 = z1 := graphMap_apply2 q1
  have h32 : graphMap q2 2 = z2 := graphMap_apply2 q2
  have h_norm3 : ‖graphMap q1 - graphMap q2‖ ^ 2 = (r1 - r2)^2 + d2 := by
    have h1 : (graphMap q1 - graphMap q2) 0 = r1 - r2 := by
      have h_diff : (graphMap q1 - graphMap q2) 0 = graphMap q1 0 - graphMap q2 0 := by exact Pi.sub_apply _ _ _
      rw [h_diff, h11, h12]
    have h2 : (graphMap q1 - graphMap q2) 1 = y1 - y2 := by
      have h_diff : (graphMap q1 - graphMap q2) 1 = graphMap q1 1 - graphMap q2 1 := by exact Pi.sub_apply _ _ _
      rw [h_diff, h21, h22]
    have h3 : (graphMap q1 - graphMap q2) 2 = z1 - z2 := by
      have h_diff : (graphMap q1 - graphMap q2) 2 = graphMap q1 2 - graphMap q2 2 := by exact Pi.sub_apply _ _ _
      rw [h_diff, h31, h32]
    have h4 : ‖graphMap q1 - graphMap q2‖ ^ 2 =
        ((graphMap q1 - graphMap q2) 0)^2 + ((graphMap q1 - graphMap q2) 1)^2 + ((graphMap q1 - graphMap q2) 2)^2 :=
      norm_sq_point3 (graphMap q1 - graphMap q2)
    rw [h4, h1, h2, h3] <;> simp [hd2] <;> ring
  have h_core : (r1 - r2)^2 + d2 ≤ (1 / (1 - ρ^2)) * d2 :=
    graphMap_lipschitz_core y1 z1 y2 z2 ρ hρ hρ1 hs1_le hs2_le
  have hC2 : C^2 = 1 / (1 - ρ^2) := by
    have h_sqrt_pos : 0 < Real.sqrt (1 - ρ^2) := Real.sqrt_pos.mpr h_pos
    have h_sq : (Real.sqrt (1 - ρ^2))^2 = 1 - ρ^2 := Real.sq_sqrt (by nlinarith)
    have h1 : C^2 = 1 / (Real.sqrt (1 - ρ^2))^2 := by
      have h2 : C = 1 / Real.sqrt (1 - ρ^2) := by rfl
      rw [h2]
      field_simp [h_sqrt_pos.ne'] <;> ring
    rw [h1, h_sq]
  have h_main : (r1 - r2)^2 + d2 ≤ C^2 * d2 := by
    rw [hC2] <;> exact h_core
  have h_dist3 : dist (graphMap q1) (graphMap q2)^2 = (r1 - r2)^2 + d2 := by
    rw [dist_eq_norm, h_norm3]
  have h_dist2 : dist q1 q2^2 = d2 := by
    rw [dist_eq_norm, h_norm2]
  rw [← h_dist3, ← h_dist2] at h_main
  have h_a : 0 ≤ dist (graphMap q1) (graphMap q2) := by positivity
  have h_b : 0 ≤ dist q1 q2 := by positivity
  have h_c : 0 ≤ C := by positivity
  have h_bc : 0 ≤ C * dist q1 q2 := mul_nonneg h_c h_b
  have h_final : dist (graphMap q1) (graphMap q2) ≤ C * dist q1 q2 := by
    by_contra h
    have h' : C * dist q1 q2 < dist (graphMap q1) (graphMap q2) := by linarith
    have h'' : (C * dist q1 q2)^2 < (dist (graphMap q1) (graphMap q2))^2 := by
      nlinarith [h_a, h_bc]
    have h''' : C^2 * dist q1 q2^2 < (dist (graphMap q1) (graphMap q2))^2 := by
      have h_eq : (C * dist q1 q2)^2 = C^2 * dist q1 q2^2 := by ring
      rw [h_eq] at h''
      exact h''
    exact absurd h_main (not_le.mpr h''')
  let C_nn : NNReal := ⟨C, hC_pos.le⟩
  have h_edist : edist (graphMap q1) (graphMap q2) ≤ (C_nn : ENNReal) * edist q1 q2 := by
    rw [edist_dist, edist_dist]
    have h1 : ENNReal.ofReal (dist (graphMap q1) (graphMap q2)) ≤
        ENNReal.ofReal (C * dist q1 q2) := ENNReal.ofReal_le_ofReal h_final
    have hC_nonneg : 0 ≤ C := by linarith
    have h2 : ENNReal.ofReal (C * dist q1 q2) =
        ENNReal.ofReal C * ENNReal.ofReal (dist q1 q2) := by
      rw [ENNReal.ofReal_mul hC_nonneg] <;> rfl
    have h3 : ENNReal.ofReal C = (C_nn : ENNReal) := by
      have h4 : ENNReal.ofReal ((C_nn : ℝ)) = (C_nn : ENNReal) := by
        exact ENNReal.ofReal_coe_nnreal
      have h5 : (C_nn : ℝ) = C := by
        exact Subtype.coe_mk C hC_pos.le
      rw [h5] at h4
      exact h4
    rw [h2, h3] at h1
    exact h1
  exact h_edist

/-- LipschitzOnWith transfers to Euclidean-normalized Hausdorff measure. -/
lemma lipschitzOnWith_muHE2_image_le {X Y : Type*}
    [EMetricSpace X] [EMetricSpace Y] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] [BorelSpace Y] {K : NNReal} {f : X → Y} {s : Set X}
    (h : LipschitzOnWith K f s) :
    (μHE[2] : Measure Y) (f '' s) ≤ (K : ENNReal)^2 * (μHE[2] : Measure X) s := by
  have h1 : (μH[2] : Measure Y) (f '' s) ≤ (K : ENNReal)^2 * (μH[2] : Measure X) s := by
    have h2 := h.hausdorffMeasure_image_le (d := (2 : ℝ)) (by norm_num)
    have h3 : (K : ENNReal)^(2 : ℝ) = (K : ENNReal)^(2 : ℕ) := by norm_cast
    rw [h3] at h2
    exact h2
  simp_rw [MeasureTheory.Measure.euclideanHausdorffMeasure_def 2, Measure.smul_apply]
  have h4 : ∀ (c : ENNReal), c * (μH[2] : Measure Y) (f '' s) ≤ (K : ENNReal)^2 * (c * (μH[2] : Measure X) s) := by
    intro c
    calc
      c * (μH[2] : Measure Y) (f '' s)
        ≤ c * ((K : ENNReal)^2 * (μH[2] : Measure X) s) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (K : ENNReal)^2 * (c * (μH[2] : Measure X) s) := by ring
  exact h4 _

end

end Kakeya.CV
