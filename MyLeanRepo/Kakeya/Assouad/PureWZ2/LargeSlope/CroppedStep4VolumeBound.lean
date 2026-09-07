import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.XZGridIncidenceStatement
import MyLeanRepo.Kakeya.Assouad.LargeSlope.Step4WitnessGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Volume bound for tube thickening ∩ horizontal slab

Bounds the volume of points within distance `r` of a line, with
`z ∈ [a,b]`. Uses a rigid transformation to align the line with the
x-axis, then a measure-preserving shear to straighten the slanted
z-slab into an axial slab. The resulting set is contained in a box
of dimensions `(b-a)/|d_z| × 2r × 2r`.

With `r = 6δ` and `|d_z| ≥ 1/2`, gives `volume ≤ 288·W·δ² = 36·√ρ·δ²`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/--
Volume bound: points within `r` of the line through `base` in direction
`direction`, with `z ∈ [a,b]`, have volume at most `4r² · 2 · (b-a)`.
-/
lemma tube_thickening_zslab_volume_bound
    {r : ℝ} (hr : 0 < r)
    {base direction : Point3} (hdir : ‖direction‖ = 1)
    {a b : ℝ} (hab : a < b)
    (hvert : (1 / 2 : ℝ) ≤ |direction (2 : Fin 3)|) :
    volume {p : Point3 |
      Metric.infDist p ({q : Point3 | ∃ t : ℝ, q = base + t • direction} : Set Point3) ≤ r ∧
      p (2 : Fin 3) ∈ Set.Icc a b} ≤
    ENNReal.ofReal (4 * r^2 * 2 * (b - a)) := by
  set W : ℝ := b - a with hW
  have hW_pos : 0 < W := by linarith
  set d_z : ℝ := direction (2 : Fin 3) with hdz
  have hdz_ne_zero : d_z ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ |d_z| := hvert
    exact abs_pos.mp (by linarith)

  let axisLine : Set Point3 := {q | ∃ t : ℝ, q = base + t • direction}
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e0axis : Set Point3 := {q | ∃ t : ℝ, q = t • e0}

  -- Helper: norm squared of a Point3
  have h_norm_sq : ∀ (z : Point3), ‖z‖ ^ 2 = (z 0)^2 + (z 1)^2 + (z 2)^2 := by
    intro z
    have h : ‖z‖ = Real.sqrt (∑ i : Fin 3, (z i)^2) := by
      simp [PiLp.norm_eq_of_L2]
    rw [h]
    rw [Real.sq_sqrt (by positivity)]
    simp [Fin.sum_univ_succ] <;> ring

  -- Distance to e0-axis equals sqrt(y1^2 + y2^2)
  have h_e0axis_dist : ∀ (y : Point3), Metric.infDist y e0axis = Real.sqrt (y 1 ^ 2 + y 2 ^ 2) := by
    intro y
    let p0 : Point3 := (y 0 : ℝ) • e0
    have hp0_in : p0 ∈ e0axis := ⟨y 0, rfl⟩
    have h_coords0 : (y - p0) 0 = 0 := by simp [p0, e0] <;> ring
    have h_coords1 : (y - p0) 1 = y 1 := by simp [p0, e0] <;> ring
    have h_coords2 : (y - p0) 2 = y 2 := by simp [p0, e0] <;> ring
    have h_dist_p0 : dist y p0 = Real.sqrt (y 1 ^ 2 + y 2 ^ 2) := by
      rw [dist_eq_norm]
      have h4 : ‖y - p0‖ ^ 2 = y 1 ^ 2 + y 2 ^ 2 := by
        rw [h_norm_sq (y - p0), h_coords0, h_coords1, h_coords2] <;> ring
      have h5 : 0 ≤ ‖y - p0‖ := by positivity
      rw [←Real.sqrt_sq h5, h4]
    have h1 : Metric.infDist y e0axis ≤ Real.sqrt (y 1 ^ 2 + y 2 ^ 2) := by
      rw [←h_dist_p0]
      exact Metric.infDist_le_dist_of_mem hp0_in
    have h_lower : ∀ (t : ℝ), Real.sqrt (y 1 ^ 2 + y 2 ^ 2) ≤ dist y (t • e0) := by
      intro t
      let z : Point3 := t • e0
      have hc0 : (y - z) 0 = y 0 - t := by simp [z, e0] <;> ring
      have hc1 : (y - z) 1 = y 1 := by simp [z, e0] <;> ring
      have hc2 : (y - z) 2 = y 2 := by simp [z, e0] <;> ring
      rw [dist_eq_norm]
      have h4 : ‖y - z‖ ^ 2 = (y 0 - t)^2 + y 1^2 + y 2^2 := by
        rw [h_norm_sq (y - z), hc0, hc1, hc2] <;> ring
      have h5 : 0 ≤ ‖y - z‖ := by positivity
      rw [←Real.sqrt_sq h5, h4]
      gcongr <;> nlinarith
    have h2 : ∀ (x : ℝ), x ∈ (dist y '' e0axis) → Real.sqrt (y 1 ^ 2 + y 2 ^ 2) ≤ x := by
      intro x hx
      rcases hx with ⟨z, hz, rfl⟩
      rcases hz with ⟨t, rfl⟩
      exact h_lower t
    have h_nonempty : e0axis.Nonempty := ⟨0, ⟨0, by simp⟩⟩
    have h3 : IsGLB (dist y '' e0axis) (Metric.infDist y e0axis) :=
      Metric.isGLB_infDist h_nonempty
    have h4 : Real.sqrt (y 1 ^ 2 + y 2 ^ 2) ≤ Metric.infDist y e0axis := by
      have h5 : Real.sqrt (y 1 ^ 2 + y 2 ^ 2) ∈ lowerBounds (dist y '' e0axis) := h2
      exact h3.right h5
    exact le_antisymm h1 h4

  -- Rigid transformation: reflection + translation
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm : ‖direction‖ = ‖e0‖ := by rw [hdir, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (direction - e0))ᗮ
  have hA_dir : A direction = e0 := Submodule.reflection_sub hnorm
  have hA_preserving : MeasurePreserving A volume volume := A.measurePreserving

  let translate : Point3 → Point3 := fun x => x - base
  have htrans_preserving : MeasurePreserving translate volume volume :=
    measurePreserving_sub_right volume base
  let rigid : Point3 → Point3 := fun x => A (translate x)
  have hrigid_isometry : Isometry rigid := by
    have hdist : ∀ (x y : Point3), dist (rigid x) (rigid y) = dist x y := by
      intro x y
      have h1 : rigid x - rigid y = A (x - y) := by
        have h2 : rigid x - rigid y = A (x - base) - A (y - base) := by rfl
        rw [h2]
        have h3 : A (x - base) - A (y - base) = A ((x - base) - (y - base)) := by
          rw [←A.map_sub] <;> rfl
        rw [h3]
        have h4 : (x - base) - (y - base) = x - y := by abel
        rw [h4]
      calc dist (rigid x) (rigid y)
        = ‖rigid x - rigid y‖ := by rw [dist_eq_norm]
      _ = ‖A (x - y)‖ := by rw [h1]
      _ = ‖x - y‖ := A.norm_map (x - y)
      _ = dist x y := by rw [dist_eq_norm]
    intro x y
    simpa [edist_dist] using congr_arg ENNReal.ofReal (hdist x y)
  have hrigid_preserving : MeasurePreserving rigid volume volume :=
    hA_preserving.comp htrans_preserving

  -- Axis line maps to e0-axis
  have haxis_image : rigid '' axisLine = e0axis := by
    ext y
    simp only [Set.mem_image, axisLine, e0axis]
    constructor
    · rintro ⟨p, ⟨t, rfl⟩, rfl⟩
      have h : rigid (base + t • direction) = t • e0 := by
        have h1 : rigid (base + t • direction) = A ((base + t • direction) - base) := by rfl
        rw [h1]
        have h2 : (base + t • direction) - base = t • direction := by abel
        rw [h2, A.map_smul, hA_dir] <;> rfl
      exact ⟨t, h⟩
    · rintro ⟨t, rfl⟩
      have h : rigid (base + t • direction) = t • e0 := by
        have h1 : rigid (base + t • direction) = A ((base + t • direction) - base) := by rfl
        rw [h1]
        have h2 : (base + t • direction) - base = t • direction := by abel
        rw [h2, A.map_smul, hA_dir] <;> rfl
      exact ⟨base + t • direction, ⟨t, rfl⟩, h⟩

  let S : Set Point3 := {p | Metric.infDist p axisLine ≤ r ∧ p (2 : Fin 3) ∈ Set.Icc a b}
  let S' : Set Point3 := rigid '' S

  -- Perpendicular norm bound in transformed coords
  have h_disk : ∀ y ∈ S', (y 1)^2 + (y 2)^2 ≤ r^2 := by
    intro y hy
    rcases hy with ⟨p, hpS, hpy⟩
    have h_y_eq : rigid p = y := hpy
    have h_dist : Metric.infDist p axisLine ≤ r := hpS.1
    have h_eq : Metric.infDist y e0axis = Metric.infDist p axisLine := by
      have h : Metric.infDist (rigid p) e0axis = Metric.infDist p axisLine := by
        rw [←haxis_image]
        exact Metric.infDist_image (hΦ := hrigid_isometry)
      have h_y : y = rigid p := h_y_eq.symm
      rw [h_y]
      exact h
    have h_main : Real.sqrt ((y 1)^2 + (y 2)^2) ≤ r := by
      rw [h_e0axis_dist y] at h_eq
      exact h_eq ▸ h_dist
    have h6 : (y 1)^2 + (y 2)^2 ≤ r^2 := by
      have h7 : 0 ≤ Real.sqrt ((y 1)^2 + (y 2)^2) := Real.sqrt_nonneg _
      have h8 : (Real.sqrt ((y 1)^2 + (y 2)^2))^2 = (y 1)^2 + (y 2)^2 :=
        Real.sq_sqrt (by positivity)
      nlinarith
    exact h6

  -- z-constraint in transformed coords
  let v : Point3 := A (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  have h_dot : ∀ (a b : Point3), inner ℝ a b = ∑ i : Fin 3, a i * b i := by
    intro a b
    have h : inner ℝ a b = ∑ i : Fin 3, inner ℝ (a i) (b i) := PiLp.inner_apply a b
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.inner_apply]
  have hv0 : v 0 = d_z := by
    have h1 : inner ℝ v e0 = v 0 := by
      rw [h_dot v e0]
      simp [e0, Fin.sum_univ_succ] <;> ring
    have h2 : inner ℝ v e0 = inner ℝ (EuclideanSpace.single (2 : Fin 3) 1) direction := by
      rw [←hA_dir]
      exact A.inner_map_map (EuclideanSpace.single (2 : Fin 3) 1) direction
    have h3 : inner ℝ (EuclideanSpace.single (2 : Fin 3) 1) direction = direction (2 : Fin 3) := by
      have h4 : inner ℝ direction (EuclideanSpace.single (2 : Fin 3) 1) = direction (2 : Fin 3) := by
        rw [h_dot direction (EuclideanSpace.single (2 : Fin 3) 1)]
        simp [Fin.sum_univ_succ] <;> ring
      have h5 : inner ℝ (EuclideanSpace.single (2 : Fin 3) 1) direction =
          inner ℝ direction (EuclideanSpace.single (2 : Fin 3) 1) := real_inner_comm _ _
      rw [h5, h4]
    linarith [h1, h2, h3]
  have h_z_constraint : ∀ y ∈ S',
      (a - base (2 : Fin 3)) ≤ v 0 * y 0 + v 1 * y 1 + v 2 * y 2 ∧
      v 0 * y 0 + v 1 * y 1 + v 2 * y 2 ≤ (b - base (2 : Fin 3)) := by
    intro y hy
    rcases hy with ⟨p, hpS, rfl⟩
    have hz2 : p (2 : Fin 3) ∈ Set.Icc a b := hpS.2
    have h_eq1 : (p - base) (2 : Fin 3) = p (2 : Fin 3) - base (2 : Fin 3) := by simp
    have h_dot1 : ∀ (a b : Point3), inner ℝ a b = ∑ i : Fin 3, a i * b i := h_dot
    have h_final : v 0 * (rigid p) 0 + v 1 * (rigid p) 1 + v 2 * (rigid p) 2 =
        (p - base) (2 : Fin 3) := by
      have h1 : v 0 * (rigid p) 0 + v 1 * (rigid p) 1 + v 2 * (rigid p) 2 = inner ℝ v (rigid p) := by
        rw [h_dot1 v (rigid p)]
        simp [Fin.sum_univ_succ] <;> ring
      rw [h1]
      have h2 : inner ℝ v (rigid p) = inner ℝ (EuclideanSpace.single (2 : Fin 3) 1) (p - base) := by
        exact A.inner_map_map (EuclideanSpace.single (2 : Fin 3) 1) (p - base)
      rw [h2]
      have h3 : inner ℝ (EuclideanSpace.single (2 : Fin 3) 1) (p - base) = (p - base) (2 : Fin 3) := by
        rw [h_dot1 (EuclideanSpace.single (2 : Fin 3) 1) (p - base)]
        simp [Fin.sum_univ_succ] <;> ring
      exact h3
    rw [h_final, h_eq1]
    have hz2' : a - base (2 : Fin 3) ≤ p (2 : Fin 3) - base (2 : Fin 3) ∧
        p (2 : Fin 3) - base (2 : Fin 3) ≤ b - base (2 : Fin 3) := by
      constructor <;> linarith [hz2.1, hz2.2]
    exact hz2'

  -- Shear transformation (upper triangular with 1s on diagonal)
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1 : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2 : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let L : Point3 →ₗ[ℝ] Point3 :=
    { toFun := fun p =>
        (p 0 + (v 1 / d_z) * p 1 + (v 2 / d_z) * p 2) • e0 + p 1 • e1 + p 2 • e2
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [e0, e1, e2, EuclideanSpace.single_apply] <;> ring
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [e0, e1, e2, EuclideanSpace.single_apply] <;> ring }
  let M : Matrix (Fin 3) (Fin 3) ℝ := !![1, v 1 / d_z, v 2 / d_z; 0, 1, 0; 0, 0, 1]
  have hM_det : M.det = 1 := by
    simp [M, Matrix.det_fin_three] <;> ring
  let basis : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have hL_mat : LinearMap.toMatrix basis basis L = M := by
    ext i j
    have h1 : (LinearMap.toMatrix basis basis L) i j = (L (basis j)) i := by
      rw [LinearMap.toMatrix_apply]
      exact PiLp.basisFun_repr 2 ℝ (Fin 3) (L (basis j)) i
    rw [h1]
    fin_cases i <;> fin_cases j <;>
      simp [L, basis, PiLp.basisFun_apply, e0, e1, e2, M,
        EuclideanSpace.single_apply, Fin.sum_univ_succ] <;> ring
  have hL_det : LinearMap.det L = 1 := by
    rw [←LinearMap.det_toMatrix basis L, hL_mat, hM_det]
  have hL_cont : Continuous L := by
    have h : Continuous (fun p : Point3 =>
        (p 0 + (v 1 / d_z) * p 1 + (v 2 / d_z) * p 2) • e0 + p 1 • e1 + p 2 • e2) := by
      fun_prop
    exact h
  have hL_meas : Measurable L := hL_cont.measurable
  have hL_preserving : MeasurePreserving L volume volume := by
    have hdet : LinearMap.det L ≠ 0 := by rw [hL_det]; norm_num
    have h_map : Measure.map L volume = ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
      MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
    rw [hL_det] at h_map
    have h' : Measure.map L volume = volume := by simpa using h_map
    exact ⟨hL_meas, h'⟩

  let S'' : Set Point3 := L '' S'

  have h_disk2 : ∀ w ∈ S'', (w 1)^2 + (w 2)^2 ≤ r^2 := by
    intro w hw
    rcases hw with ⟨y, hy, rfl⟩
    have h1 : (L y) 1 = y 1 := by
      simp [L, e0, e1, e2, EuclideanSpace.single_apply] <;> ring
    have h2 : (L y) 2 = y 2 := by
      simp [L, e0, e1, e2, EuclideanSpace.single_apply] <;> ring
    rw [h1, h2]
    exact h_disk y hy

  have h_t_constraint : ∀ w ∈ S'',
      (a - base (2 : Fin 3)) ≤ d_z * w (0 : Fin 3) ∧
      d_z * w (0 : Fin 3) ≤ (b - base (2 : Fin 3)) := by
    intro w hw
    rcases hw with ⟨y, hy, rfl⟩
    have h_zc := h_z_constraint y hy
    have h_t : (L y) 0 = y 0 + (v 1 * y 1 + v 2 * y 2) / d_z := by
      simp [L, e0, e1, e2, EuclideanSpace.single_apply] <;> ring
    have h_eq : d_z * (L y) 0 = v 0 * y 0 + v 1 * y 1 + v 2 * y 2 := by
      rw [h_t, hv0] <;> field_simp [hdz_ne_zero] <;> ring
    rw [h_eq]
    exact h_zc

  -- Diameter bounds
  have h_diam0 : ∀ (w1 w2 : Point3), w1 ∈ S'' → w2 ∈ S'' →
      |w1 0 - w2 0| ≤ W / |d_z| := by
    intro w1 w2 hw1 hw2
    have h1 : (a - base (2 : Fin 3)) ≤ d_z * w1 (0 : Fin 3) := (h_t_constraint w1 hw1).1
    have h2 : d_z * w1 (0 : Fin 3) ≤ (b - base (2 : Fin 3)) := (h_t_constraint w1 hw1).2
    have h3 : (a - base (2 : Fin 3)) ≤ d_z * w2 (0 : Fin 3) := (h_t_constraint w2 hw2).1
    have h4 : d_z * w2 (0 : Fin 3) ≤ (b - base (2 : Fin 3)) := (h_t_constraint w2 hw2).2
    have h5 : |d_z * w1 (0 : Fin 3) - d_z * w2 (0 : Fin 3)| ≤ W := by
      have h6 : d_z * w1 (0 : Fin 3) ∈ Set.Icc (a - base (2 : Fin 3)) (b - base (2 : Fin 3)) := ⟨h1, h2⟩
      have h7 : d_z * w2 (0 : Fin 3) ∈ Set.Icc (a - base (2 : Fin 3)) (b - base (2 : Fin 3)) := ⟨h3, h4⟩
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    have h91 : d_z * w1 (0 : Fin 3) - d_z * w2 (0 : Fin 3) = d_z * (w1 (0 : Fin 3) - w2 (0 : Fin 3)) := by ring
    rw [h91] at h5
    have h9 : |d_z * (w1 (0 : Fin 3) - w2 (0 : Fin 3))| = |d_z| * |w1 (0 : Fin 3) - w2 (0 : Fin 3)| := by
      rw [abs_mul]
    rw [h9] at h5
    have h10 : |w1 (0 : Fin 3) - w2 (0 : Fin 3)| ≤ W / |d_z| := by
      calc |w1 (0 : Fin 3) - w2 (0 : Fin 3)|
        = (|d_z| * |w1 (0 : Fin 3) - w2 (0 : Fin 3)|) / |d_z| := by field_simp [hdz_ne_zero] <;> ring
      _ ≤ W / |d_z| := by gcongr
    exact h10

  have h_abs_le_r : ∀ (w : Point3), w ∈ S'' → |w 1| ≤ r ∧ |w 2| ≤ r := by
    intro w hw
    have h : (w 1)^2 + (w 2)^2 ≤ r^2 := h_disk2 w hw
    have hnon1 : 0 ≤ (w 1)^2 := by positivity
    have hnon2 : 0 ≤ (w 2)^2 := by positivity
    have h1 : (w 1)^2 ≤ r^2 := by linarith
    have h2 : (w 2)^2 ≤ r^2 := by linarith
    have hr : 0 ≤ r := by linarith
    have h3 : |w 1| ≤ r := by
      calc |w 1|
        = Real.sqrt ((w 1)^2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (r^2) := Real.sqrt_le_sqrt h1
      _ = r := by rw [Real.sqrt_sq hr]
    have h4 : |w 2| ≤ r := by
      calc |w 2|
        = Real.sqrt ((w 2)^2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (r^2) := Real.sqrt_le_sqrt h2
      _ = r := by rw [Real.sqrt_sq hr]
    exact ⟨h3, h4⟩

  have h_diam12 : ∀ (w1 w2 : Point3), w1 ∈ S'' → w2 ∈ S'' →
      |w1 1 - w2 1| ≤ 2 * r ∧ |w1 2 - w2 2| ≤ 2 * r := by
    intro w1 w2 hw1 hw2
    have h1 := (h_abs_le_r w1 hw1).1
    have h2 := (h_abs_le_r w2 hw2).1
    have h3 := (h_abs_le_r w1 hw1).2
    have h4 := (h_abs_le_r w2 hw2).2
    constructor
    · have h5 : |w1 1 - w2 1| ≤ |w1 1| + |w2 1| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (w1 1) (-(w2 1))
      calc |w1 1 - w2 1|
        ≤ |w1 1| + |w2 1| := h5
        _ ≤ r + r := by linarith
        _ = 2 * r := by ring
    · have h5 : |w1 2 - w2 2| ≤ |w1 2| + |w2 2| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (w1 2) (-(w2 2))
      calc |w1 2 - w2 2|
        ≤ |w1 2| + |w2 2| := h5
        _ ≤ r + r := by linarith
        _ = 2 * r := by ring

  -- Transfer to plain function type for diameter product bound
  let S_pi : Set (Fin 3 → ℝ) := WithLp.ofLp '' S''
  have hpres_toLp : MeasurePreserving (WithLp.toLp 2) volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have h1_image : (WithLp.toLp 2) '' S_pi = S'' := by
    ext y
    simp only [Set.mem_image, S_pi]
    constructor
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      have h : WithLp.toLp 2 (WithLp.ofLp w) = w := WithLp.toLp_ofLp 2 w
      rw [h] <;> exact hw
    · intro hy
      exact ⟨WithLp.ofLp y, ⟨y, hy, rfl⟩, WithLp.toLp_ofLp 2 y⟩
  -- Volume equalities via MeasurePreserving.measure_preimage

  -- S is measurable
  have hS_meas : MeasurableSet S := by
    have h1 : Measurable (fun p : Point3 => Metric.infDist p axisLine) :=
      (Metric.continuous_infDist_pt axisLine).measurable
    have h2 : Measurable (fun p : Point3 => p (2 : Fin 3)) :=
      (PiLp.continuous_apply 2 (fun _ => ℝ) (2 : Fin 3)).measurable
    have hIic_meas : MeasurableSet (Set.Iic r) := isClosed_Iic.measurableSet
    have hIcc_meas : MeasurableSet (Set.Icc a b) := isClosed_Icc.measurableSet
    exact hIic_meas.preimage h1 |>.inter (hIcc_meas.preimage h2)

  -- rigid as MeasurableEquiv
  let rigid_homeo : Point3 ≃ₜ Point3 :=
    { toFun := rigid
      invFun := fun y => A.symm y + base
      left_inv := by
        intro x
        dsimp only [rigid, translate]
        have h : A.symm (A (x - base)) = x - base := A.left_inv (x - base)
        rw [h] <;> exact sub_add_cancel x base
      right_inv := by
        intro y
        dsimp only [rigid, translate]
        have h1 : (A.symm y + base) - base = A.symm y := by
          ext i; fin_cases i <;> simp
        rw [h1] <;> exact A.right_inv y
      continuous_toFun := hrigid_isometry.continuous
      continuous_invFun := A.symm.continuous.add continuous_const }
  let rigid_equiv : Point3 ≃ᵐ Point3 := rigid_homeo.toMeasurableEquiv
  have hS'_meas : MeasurableSet S' := by
    have h_eq : S' = rigid_equiv '' S := by rfl
    rw [h_eq]
    exact rigid_equiv.measurableSet_image.mpr hS_meas
  have h_vol3 : volume S = volume S' := by
    have h_preimage : rigid ⁻¹' S' = S := by
      ext x
      have hS'_def : S' = rigid '' S := by rfl
      simp only [Set.mem_preimage, hS'_def, Set.mem_image]
      constructor
      · rintro ⟨y, hy, h_eq⟩
        have h : rigid x = rigid y := h_eq.symm
        have h_inj : x = y := hrigid_isometry.injective h
        rw [h_inj]; exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have h : volume (rigid ⁻¹' S') = volume S' :=
      hrigid_preserving.measure_preimage hS'_meas.nullMeasurableSet
    rw [h_preimage] at h
    exact h

  -- L volume via addHaar_image_linearMap (det = 1)
  have h_vol2 : volume S' = volume S'' := by
    have h : volume (L '' S') = ENNReal.ofReal |LinearMap.det L| * volume S' :=
      MeasureTheory.Measure.addHaar_image_linearMap volume L S'
    rw [h, hL_det] <;> simp

  -- S'' measurable
  have hL_det_ne_zero : LinearMap.det L ≠ 0 := by rw [hL_det]; norm_num
  let L_cl : Point3 ≃ₗ[ℝ] Point3 := L.equivOfDetNeZero hL_det_ne_zero
  let L_meas_equiv : Point3 ≃ᵐ Point3 :=
    { toFun := L,
      invFun := L_cl.symm,
      left_inv := L_cl.left_inv,
      right_inv := L_cl.right_inv,
      measurable_toFun := hL_meas,
      measurable_invFun := (L_cl.symm.toLinearMap.continuous_of_finiteDimensional).measurable }
  have hS''_meas : MeasurableSet S'' :=
    L_meas_equiv.measurableSet_image.mpr hS'_meas

  -- WithLp equivalence: Point3 → (Fin 3 → ℝ)
  -- WithLp.ofLp : Point3 → (Fin 3 → ℝ)
  -- WithLp.toLp 2 : (Fin 3 → ℝ) → Point3
  let toLp_homeo : Point3 ≃ₜ (Fin 3 → ℝ) :=
    { toFun := WithLp.ofLp,
      invFun := WithLp.toLp 2,
      left_inv := WithLp.toLp_ofLp 2,
      right_inv := WithLp.ofLp_toLp 2,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop }
  let toLp_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) := toLp_homeo.toMeasurableEquiv
  have hSpi_meas : MeasurableSet S_pi := by
    have h_eq : S_pi = toLp_equiv '' S'' := by rfl
    rw [h_eq]
    exact toLp_equiv.measurableSet_image.mpr hS''_meas
  have h_vol_eq : volume S'' = volume S_pi := by
    have h_meas_img : MeasurableSet ((WithLp.toLp 2) '' S_pi) := by
      have h_eq : (WithLp.toLp 2) '' S_pi = toLp_equiv.symm '' S_pi := by rfl
      rw [h_eq]
      exact toLp_equiv.symm.measurableSet_image.mpr hSpi_meas
    have h_preimage : (WithLp.toLp 2) ⁻¹' ((WithLp.toLp 2) '' S_pi) = S_pi := by
      ext x; simp [toLp_equiv.symm.injective]
    have h : volume ((WithLp.toLp 2) ⁻¹' ((WithLp.toLp 2) '' S_pi)) =
        volume ((WithLp.toLp 2) '' S_pi) :=
      hpres_toLp.measure_preimage h_meas_img.nullMeasurableSet
    rw [h_preimage] at h
    rw [h1_image] at h
    exact h.symm

  have h_eval_eq : ∀ (i : Fin 3), Function.eval i '' S_pi = (fun x : Point3 => x i) '' S'' := by
    intro i
    ext z
    simp only [Set.mem_image, S_pi, Function.eval_apply]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨WithLp.ofLp w, ⟨w, hw, rfl⟩, rfl⟩
  have h_diam0' : EMetric.diam (Function.eval (0 : Fin 3) '' S_pi) ≤ ENNReal.ofReal (W / |d_z|) := by
    rw [h_eval_eq 0]
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    rcases hx with ⟨w1, hw1, rfl⟩
    rcases hy with ⟨w2, hw2, rfl⟩
    have h : dist (w1 0) (w2 0) = |w1 0 - w2 0| := by
      rw [Real.dist_eq] <;> rfl
    rw [h]
    exact h_diam0 w1 w2 hw1 hw2
  have h_diam1' : EMetric.diam (Function.eval (1 : Fin 3) '' S_pi) ≤ ENNReal.ofReal (2 * r) := by
    rw [h_eval_eq 1]
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    rcases hx with ⟨w1, hw1, rfl⟩
    rcases hy with ⟨w2, hw2, rfl⟩
    have h : dist (w1 1) (w2 1) = |w1 1 - w2 1| := by
      rw [Real.dist_eq] <;> rfl
    rw [h]
    exact (h_diam12 w1 w2 hw1 hw2).1
  have h_diam2' : EMetric.diam (Function.eval (2 : Fin 3) '' S_pi) ≤ ENNReal.ofReal (2 * r) := by
    rw [h_eval_eq 2]
    apply Metric.ediam_le_of_forall_dist_le
    intro x hx y hy
    rcases hx with ⟨w1, hw1, rfl⟩
    rcases hy with ⟨w2, hw2, rfl⟩
    have h : dist (w1 2) (w2 2) = |w1 2 - w2 2| := by
      rw [Real.dist_eq] <;> rfl
    rw [h]
    exact (h_diam12 w1 w2 hw1 hw2).2
  have h_main : volume S_pi ≤ ∏ i : Fin 3, EMetric.diam (Function.eval i '' S_pi) :=
    Real.volume_pi_le_prod_diam S_pi
  have h_pos1 : 0 ≤ W / |d_z| := by positivity
  have h_pos2 : 0 ≤ (2 * r : ℝ) := by positivity
  have h_ofReal_mul1 : ENNReal.ofReal ((W / |d_z|) * (2 * r)) =
      ENNReal.ofReal (W / |d_z|) * ENNReal.ofReal (2 * r) := by
    rw [ENNReal.ofReal_mul h_pos1]
  have h_pos3 : 0 ≤ (W / |d_z|) * (2 * r) := by positivity
  have h_ofReal_mul2 : ENNReal.ofReal (((W / |d_z|) * (2 * r)) * (2 * r)) =
      ENNReal.ofReal ((W / |d_z|) * (2 * r)) * ENNReal.ofReal (2 * r) := by
    rw [ENNReal.ofReal_mul h_pos3]
  have h_prod : (∏ i : Fin 3, EMetric.diam (Function.eval i '' S_pi)) ≤
      ENNReal.ofReal ((W / |d_z|) * (2 * r) * (2 * r)) := by
    have h_step1 : EMetric.diam (Function.eval (0 : Fin 3) '' S_pi) *
          EMetric.diam (Function.eval (1 : Fin 3) '' S_pi) ≤
        ENNReal.ofReal (W / |d_z|) * ENNReal.ofReal (2 * r) :=
      mul_le_mul' h_diam0' h_diam1'
    have h_step2 : (EMetric.diam (Function.eval (0 : Fin 3) '' S_pi) *
          EMetric.diam (Function.eval (1 : Fin 3) '' S_pi)) *
          EMetric.diam (Function.eval (2 : Fin 3) '' S_pi) ≤
        (ENNReal.ofReal (W / |d_z|) * ENNReal.ofReal (2 * r)) * ENNReal.ofReal (2 * r) :=
      mul_le_mul' h_step1 h_diam2'
    have h_simp : (∏ i : Fin 3, EMetric.diam (Function.eval i '' S_pi)) =
        EMetric.diam (Function.eval (0 : Fin 3) '' S_pi) *
        EMetric.diam (Function.eval (1 : Fin 3) '' S_pi) *
        EMetric.diam (Function.eval (2 : Fin 3) '' S_pi) := by
      simp [Fin.prod_univ_succ] <;> ring
    rw [h_simp]
    have h_ofReal_mul1 : ENNReal.ofReal (W / |d_z|) * ENNReal.ofReal (2 * r) =
        ENNReal.ofReal ((W / |d_z|) * (2 * r)) := by
      rw [ENNReal.ofReal_mul h_pos1]
    have h_ofReal_mul2 : ENNReal.ofReal ((W / |d_z|) * (2 * r)) * ENNReal.ofReal (2 * r) =
        ENNReal.ofReal (((W / |d_z|) * (2 * r)) * (2 * r)) := by
      rw [ENNReal.ofReal_mul h_pos3]
    have h_final : (ENNReal.ofReal (W / |d_z|) * ENNReal.ofReal (2 * r)) * ENNReal.ofReal (2 * r) =
        ENNReal.ofReal ((W / |d_z|) * (2 * r) * (2 * r)) := by
      calc (ENNReal.ofReal (W / |d_z|) * ENNReal.ofReal (2 * r)) * ENNReal.ofReal (2 * r)
        = ENNReal.ofReal ((W / |d_z|) * (2 * r)) * ENNReal.ofReal (2 * r) := by rw [h_ofReal_mul1]
      _ = ENNReal.ofReal (((W / |d_z|) * (2 * r)) * (2 * r)) := by rw [h_ofReal_mul2]
      _ = ENNReal.ofReal ((W / |d_z|) * (2 * r) * (2 * r)) := by rfl
    exact h_step2.trans (le_of_eq h_final)
  have h_vol : volume S_pi ≤ ENNReal.ofReal ((W / |d_z|) * (2 * r) * (2 * r)) :=
    h_main.trans h_prod

  rw [h_vol3, h_vol2, h_vol_eq]
  have h7 : 1 / |d_z| ≤ 2 := by
    have h8 : (1 / 2 : ℝ) ≤ |d_z| := hvert
    have h9 : 0 < |d_z| := by linarith
    have h10 : 1 / |d_z| ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) h8
    rw [show (1 / (1 / 2 : ℝ)) = 2 by norm_num] at h10
    exact h10
  have hW_nonneg : 0 ≤ W := by linarith
  have hdiv : W / |d_z| ≤ 2 * W := by
    calc W / |d_z| = W * (1 / |d_z|) := by ring
    _ ≤ W * 2 := by gcongr
    _ = 2 * W := by ring
  have h9 : (W / |d_z|) * (2 * r) * (2 * r) ≤ 4 * r^2 * 2 * W := by
    calc (W / |d_z|) * (2 * r) * (2 * r)
      = 4 * r^2 * (W / |d_z|) := by ring
    _ ≤ 4 * r^2 * (2 * W) := by gcongr
    _ = 4 * r^2 * 2 * W := by ring
  exact h_vol.trans (ENNReal.ofReal_le_ofReal h9)

end Kakeya.Assouad

end
