import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure
import Mathlib.Tactic

/-!
# Geometric bounds for the anisotropic rescaling image

Provides coordinate-wise bounds and box volume estimates for the image
of the unit-ball tube configuration under `anisotropicRescalingMap`.
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Assouad

/-- Projection of `point3` onto coordinates. -/
private lemma point3_coord (x y z : ℝ) :
    (point3 x y z) 0 = x ∧ (point3 x y z) 1 = y ∧ (point3 x y z) 2 = z := by
  constructor
  · simp [point3, EuclideanSpace.single_apply] <;> ring
  · constructor
    · simp [point3, EuclideanSpace.single_apply] <;> ring
    · simp [point3, EuclideanSpace.single_apply] <;> ring

/-- Each coordinate of a Euclidean point is bounded by its norm. -/
private lemma coord_le_norm {p : Point3} {i : Fin 3} (hp : ‖p‖ ≤ 1) : |p i| ≤ 1 := by
  have h2 : (p i)^2 ≤ ∑ j : Fin 3, (p j)^2 := by
    have h3 : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ (p j)^2 := fun j _ => sq_nonneg _
    exact Finset.single_le_sum h3 (Finset.mem_univ i)
  have h1 : (p i)^2 ≤ ‖p‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq] at *
    <;> exact h2
  have h4 : 0 ≤ ‖p‖ := by positivity
  have h5 : |p i| ≤ ‖p‖ := by
    have h6 : |p i|^2 ≤ ‖p‖^2 := by simpa [sq_abs] using h1
    nlinarith
  exact h5.trans hp

/-- Triangle inequality for real absolute values. -/
private lemma abs_triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h1 : a + b ≤ |a| + |b| := by
    have h2 : a ≤ |a| := le_abs_self a
    have h3 : b ≤ |b| := le_abs_self b
    linarith
  have h4 : -(a + b) ≤ |a| + |b| := by
    have h5 : -a ≤ |a| := by
      have h6 : |-a| = |a| := by rw [abs_neg]
      have h7 : -a ≤ |-a| := le_abs_self (-a)
      rw [h6] at h7; exact h7
    have h8 : -b ≤ |b| := by
      have h9 : |-b| = |b| := by rw [abs_neg]
      have h10 : -b ≤ |-b| := le_abs_self (-b)
      rw [h9] at h10; exact h10
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- x-coordinate bound: |x'| ≤ 2. -/
lemma anisotropicImage_x_bound
    {g : SlopeFunction} (hg_norm : g.IsNormalized)
    {c d m : ℝ} (hcd : c < d)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    {p : Point3} (hp_unit : ‖p‖ ≤ 1) :
    |(anisotropicRescalingMap g c d m p) 0| ≤ 2 := by
  set mid := c + (d - c) / 2 with hmid
  have hc1 : -1 ≤ c := (h_sub ⟨by linarith, by linarith⟩).1
  have hd1 : d ≤ 1 := (h_sub ⟨by linarith, by linarith⟩).2
  have hmid_in : mid ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith
  have hg_mid : |g mid| ≤ 1 := (hg_norm mid hmid_in).1
  have hx : |p 0| ≤ 1 := coord_le_norm hp_unit
  have hy : |p 1| ≤ 1 := coord_le_norm hp_unit
  set q := anisotropicRescalingMap g c d m p with hq
  have hq0 : q 0 = p 0 + g mid * p 1 := (point3_coord _ _ _).1
  rw [hq0]
  have h_tri : |p 0 + g mid * p 1| ≤ |p 0| + |g mid * p 1| := abs_triangle _ _
  have h_mul : |g mid * p 1| = |g mid| * |p 1| := abs_mul _ _
  calc
    |p 0 + g mid * p 1|
        ≤ |p 0| + |g mid * p 1| := h_tri
    _ = |p 0| + |g mid| * |p 1| := by rw [h_mul]
    _ ≤ 1 + 1 * 1 := by gcongr <;> linarith
    _ = 2 := by norm_num

/-- y-coordinate bound: |y'| ≤ m*(d-c)/2. -/
lemma anisotropicImage_y_bound
    {g : SlopeFunction} {c d m : ℝ} (hm_nonneg : 0 ≤ m) (hcd : c < d)
    {p : Point3} (hp_unit : ‖p‖ ≤ 1) :
    |(anisotropicRescalingMap g c d m p) 1| ≤ m * (d - c) / 2 := by
  have hy : |p 1| ≤ 1 := coord_le_norm hp_unit
  have h_pos : 0 ≤ m * (d - c) / 2 := by positivity
  set q := anisotropicRescalingMap g c d m p with hq
  have hq1 : q 1 = m * (d - c) / 2 * p 1 := (point3_coord _ _ _).2.1
  rw [hq1]
  calc
    |m * (d - c) / 2 * p 1|
        = |m * (d - c) / 2| * |p 1| := by rw [abs_mul]
    _ = (m * (d - c) / 2) * |p 1| := by rw [abs_of_nonneg h_pos]
    _ ≤ (m * (d - c) / 2) * 1 := by gcongr
    _ = m * (d - c) / 2 := by ring

/-- z-coordinate bound: z' ∈ [-1,1]. -/
lemma anisotropicImage_z_bound
    {g : SlopeFunction} {c d m : ℝ} (hcd : c < d)
    {p : Point3} (hp_z : p 2 ∈ Set.Icc c d) :
    (anisotropicRescalingMap g c d m p) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 : c ≤ p 2 := hp_z.1
  have h2 : p 2 ≤ d := hp_z.2
  have h3 : 0 < d - c := by linarith
  set q := anisotropicRescalingMap g c d m p with hq
  have hq2 : q 2 = 2 * (p 2 - c) / (d - c) - 1 := (point3_coord _ _ _).2.2
  rw [hq2]
  constructor
  · have h4 : 0 ≤ 2 * (p 2 - c) / (d - c) := by positivity
    linarith
  · have h5 : 2 * (p 2 - c) ≤ 2 * (d - c) := by linarith
    have h6 : 2 * (p 2 - c) / (d - c) ≤ 2 := by
      calc
        2 * (p 2 - c) / (d - c) ≤ 2 * (d - c) / (d - c) := by gcongr
        _ = 2 := by field_simp [h3.ne'] <;> ring
    linarith

/--
The image of a unit-ball point whose height lies in the `delta`-extended slab
has norm at most two.

The extension costs `2 * delta / (d - c)` in the normalized vertical
coordinate.  Under the covering hypotheses this is at most `1 / 4`.  The
horizontal shear is estimated jointly using the source unit-ball inequality,
rather than by separately maximizing both source coordinates.
-/
lemma anisotropicImage_extended_slab_norm_le_two
    {g : SlopeFunction} (hg_norm : g.IsNormalized)
    {c d m delta : ℝ}
    (hdelta : 0 ≤ delta) (hcd : c < d)
    (hm_nonneg : 0 ≤ m) (hm_one : m ≤ 1)
    (h_dc : d - c ≤ 1 / 25)
    (hrho_small : 2 * delta / (d - c) ≤ 1 / 4)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    {p : Point3} (hp_unit : ‖p‖ ≤ 1)
    (hp_z : p 2 ∈ Set.Icc (c - delta) (d + delta)) :
    ‖anisotropicRescalingMap g c d m p‖ ≤ 2 := by
  let q := anisotropicRescalingMap g c d m p
  let mid : ℝ := c + (d - c) / 2
  have hmid_cd : mid ∈ Set.Icc c d := by
    constructor <;> dsimp only [mid] <;> linarith
  have hmid_window : mid ∈ Set.Icc (-1 : ℝ) 1 :=
    h_sub hmid_cd
  have hg_mid : |g mid| ≤ 1 :=
    (hg_norm mid hmid_window).1
  have hq0 :
      q 0 = p 0 + g mid * p 1 := by
    simp [q, mid, anisotropicRescalingMap, point3]
  have hx_sq :
      (q 0) ^ 2 ≤ 2 * ((p 0) ^ 2 + (p 1) ^ 2) := by
    rw [hq0]
    have hcauchy :
        (p 0 + g mid * p 1) ^ 2 ≤
          (1 + (g mid) ^ 2) * ((p 0) ^ 2 + (p 1) ^ 2) := by
      nlinarith [sq_nonneg (p 0 * g mid - p 1)]
    have hg_sq : (g mid) ^ 2 ≤ 1 := by
      nlinarith [abs_le.mp hg_mid]
    have hp_xy_nonneg : 0 ≤ (p 0) ^ 2 + (p 1) ^ 2 := by
      positivity
    nlinarith
  have hy_raw : |q 1| ≤ m * (d - c) / 2 :=
    anisotropicImage_y_bound hm_nonneg hcd hp_unit
  have hy_scale : m * (d - c) / 2 ≤ 1 / 50 := by
    calc
      m * (d - c) / 2
          ≤ 1 * (d - c) / 2 := by
            gcongr
      _ ≤ 1 * (1 / 25 : ℝ) / 2 := by
            gcongr
      _ = 1 / 50 := by norm_num
  have hy : |q 1| ≤ 1 / 50 := hy_raw.trans hy_scale
  have hdc_pos : 0 < d - c := by
    linarith
  have hrho_nonneg : 0 ≤ 2 * delta / (d - c) := by
    positivity
  have hq2 :
      q 2 = 2 * (p 2 - c) / (d - c) - 1 := by
    simp [q, anisotropicRescalingMap, point3]
  have hz_lower :
      -(1 + 2 * delta / (d - c)) ≤ q 2 := by
    rw [hq2]
    have hp_lower : -delta ≤ p 2 - c := by
      linarith [hp_z.1]
    have hdiv :
        2 * (-delta) / (d - c) ≤
          2 * (p 2 - c) / (d - c) := by
      gcongr
    have hneg :
        2 * (-delta) / (d - c) =
          -(2 * delta / (d - c)) := by
      ring
    rw [hneg] at hdiv
    linarith
  have hz_upper :
      q 2 ≤ 1 + 2 * delta / (d - c) := by
    rw [hq2]
    have hp_upper : p 2 - c ≤ d - c + delta := by
      linarith [hp_z.2]
    have hdiv :
        2 * (p 2 - c) / (d - c) ≤
          2 * (d - c + delta) / (d - c) := by
      gcongr
    have hsimp :
        2 * (d - c + delta) / (d - c) =
          2 + 2 * delta / (d - c) := by
      field_simp [hdc_pos.ne']
    rw [hsimp] at hdiv
    linarith
  have hrho_bound : 1 + 2 * delta / (d - c) ≤ 5 / 4 := by
    linarith
  have hz : |q 2| ≤ 5 / 4 := by
    rw [abs_le]
    constructor
    · exact (neg_le_neg hrho_bound).trans hz_lower
    · exact hz_upper.trans hrho_bound
  have hy_sq : (q 1) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 50)] using hy
  have hz_sq : (q 2) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 4)] using hz
  have hnorm_sq :
      ‖q‖ ^ 2 = (q 0) ^ 2 + (q 1) ^ 2 + (q 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hp_norm_sq :
      ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have hp_sq : ‖p‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg p]
  have hp_xy : (p 0) ^ 2 + (p 1) ^ 2 ≤ 1 := by
    rw [hp_norm_sq] at hp_sq
    nlinarith [sq_nonneg (p 2)]
  have hsq : ‖q‖ ^ 2 ≤ 2 ^ 2 := by
    rw [hnorm_sq]
    nlinarith [show (0 : ℝ) < 4 -
      (2 + (1 / 50 : ℝ) ^ 2 + (5 / 4 : ℝ) ^ 2) by norm_num]
  exact (sq_le_sq₀ (norm_nonneg q) (by norm_num)).mp hsq

/--
Direct tube-axis form of `anisotropicImage_extended_slab_norm_le_two`.

An axis point of a unit-ball tube belongs to its carrier, so its source norm
is at most one.  This is the form consumed by the clipped endpoint cover.
-/
lemma anisotropicImage_tube_axis_norm_le_two
    {g : SlopeFunction} (hg_norm : g.IsNormalized)
    {c d m delta : ℝ}
    (hdelta : 0 ≤ delta) (hcd : c < d)
    (hm_nonneg : 0 ≤ m) (hm_one : m ≤ 1)
    (h_dc : d - c ≤ 1 / 25)
    (hrho_small : 2 * delta / (d - c) ≤ 1 / 4)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (T : Kakeya.DeltaTube delta) (hT_ball : T.IsInUnitBall)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ht_z :
      (T.base + t • T.direction) 2 ∈
        Set.Icc (c - delta) (d + delta)) :
    ‖anisotropicRescalingMap g c d m
        (T.base + t • T.direction)‖ ≤ 2 := by
  let p : Point3 := T.base + t • T.direction
  have hp_axis : p ∈ Kakeya.unitSegment T.base T.direction :=
    ⟨t, ht, rfl⟩
  have hp_carrier : p ∈ T.carrier :=
    Metric.mem_cthickening_of_dist_le
      p p delta _ hp_axis (by simpa using hdelta)
  have hp_ball : p ∈ Metric.closedBall (0 : Point3) 1 :=
    hT_ball hp_carrier
  have hp_unit : ‖p‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hp_ball
  exact anisotropicImage_extended_slab_norm_le_two
    hg_norm hdelta hcd hm_nonneg hm_one h_dc hrho_small h_sub
    hp_unit ht_z

/-- Volume bound for the anisotropic image.

The image lies in a box of dimensions 4 × m*(d-c) × 2. -/
lemma anisotropicImage_volume_bound
    {g : SlopeFunction} (hg_norm : g.IsNormalized)
    {c d m : ℝ} (hcd : c < d) (hm_nonneg : 0 ≤ m)
    (h_sub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    {E : Set Point3} (hE_unit : E ⊆ Metric.closedBall (0 : Point3) 1)
    (hE_slab : E ⊆ horizontalSlab c d) :
    volume (anisotropicRescalingMap g c d m '' E) ≤
      ENNReal.ofReal (4 * (m * (d - c)) * 2) := by
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  let lo : Fin 3 → ℝ := fun i =>
    match i with | 0 => -2 | 1 => -(m * (d - c) / 2) | 2 => -1
  let hi : Fin 3 → ℝ := fun i =>
    match i with | 0 => 2 | 1 => m * (d - c) / 2 | 2 => 1
  let box : Set Point3 := toLp '' Set.Icc lo hi

  have h_pos_y : 0 ≤ m * (d - c) / 2 := by positivity
  have hlohi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i
    · exact by norm_num
    · dsimp only [lo, hi]
      exact neg_le_self h_pos_y
    · exact by norm_num

  have h_image_sub : anisotropicRescalingMap g c d m '' E ⊆ box := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have hp_unit : ‖p‖ ≤ 1 := by
      have h : p ∈ Metric.closedBall (0 : Point3) 1 := hE_unit hp
      have h2 : dist p (0 : Point3) ≤ 1 := by simpa [Metric.mem_closedBall] using h
      have h3 : dist p (0 : Point3) = ‖p‖ := by
        simp [dist_zero_right]
      rw [h3] at h2
      exact h2
    have hp_z : p 2 ∈ Set.Icc c d := hE_slab hp
    set q := anisotropicRescalingMap g c d m p with hq
    have hx : |q 0| ≤ 2 := anisotropicImage_x_bound hg_norm hcd h_sub hp_unit
    have hy' : |q 1| ≤ m * (d - c) / 2 := anisotropicImage_y_bound hm_nonneg hcd hp_unit
    have hz : q 2 ∈ Set.Icc (-1 : ℝ) 1 := anisotropicImage_z_bound hcd hp_z
    have h_in : q.ofLp ∈ Set.Icc lo hi := by
      simp only [Set.mem_Icc]
      constructor
      · intro i
        fin_cases i
        · simp [lo, hi]; exact abs_le.mp hx |>.1
        · simp [lo, hi]; exact abs_le.mp hy' |>.1
        · simp [lo, hi]; exact hz.1
      · intro i
        fin_cases i
        · simp [lo, hi]; exact abs_le.mp hx |>.2
        · simp [lo, hi]; exact abs_le.mp hy' |>.2
        · simp [lo, hi]; exact hz.2
    have h_eq : toLp q.ofLp = q := WithLp.toLp_ofLp 2 q
    exact ⟨q.ofLp, h_in, h_eq⟩

  have h_vol_box : volume box = ENNReal.ofReal (4 * (m * (d - c)) * 2) := by
    have hpreserving : MeasurePreserving toLp :=
      PiLp.volume_preserving_toLp (ι := Fin 3)
    have hinjective : Function.Injective toLp := by
      intro x y hxy
      simpa [toLp, WithLp.toLp_injective] using hxy
    have hcontinuous : Continuous toLp :=
      PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
    have himage_measurable : MeasurableSet (toLp '' Set.Icc lo hi) := by
      have himage : toLp '' Set.Icc lo hi =
          (fun x : Point3 => x.ofLp) ⁻¹' Set.Icc lo hi := by
        ext y
        simp only [toLp, Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa [WithLp.ofLp_toLp] using hx
        · intro hy
          exact ⟨y.ofLp, hy, by simp [WithLp.ofLp_toLp]⟩
      rw [himage]
      exact (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable measurableSet_Icc
    have hvolume : volume (toLp '' Set.Icc lo hi) = volume (Set.Icc lo hi) := by
      calc
        volume (toLp '' Set.Icc lo hi)
            = Measure.map toLp volume (toLp '' Set.Icc lo hi) := by
              rw [hpreserving.map_eq]
        _ = volume (toLp ⁻¹' (toLp '' Set.Icc lo hi)) :=
          Measure.map_apply hcontinuous.measurable himage_measurable
        _ = volume (Set.Icc lo hi) := by
          rw [Set.preimage_image_eq _ hinjective]
    rw [hvolume, Real.volume_Icc_pi, Fin.prod_univ_three]
    have h_dims : (hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2) =
        4 * (m * (d - c)) * 2 := by
      simp [lo, hi] <;> ring
    have h_nonneg : ∀ i, 0 ≤ hi i - lo i := by
      intro i; exact sub_nonneg.mpr (hlohi i)
    have h_a : 0 ≤ hi 0 - lo 0 := h_nonneg 0
    have h_b : 0 ≤ hi 1 - lo 1 := h_nonneg 1
    have h_c : 0 ≤ hi 2 - lo 2 := h_nonneg 2
    have h_step1 : ENNReal.ofReal (hi 0 - lo 0) * ENNReal.ofReal (hi 1 - lo 1) =
        ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1)) :=
      (ENNReal.ofReal_mul h_a).symm
    have h6 : ENNReal.ofReal (hi 0 - lo 0) * ENNReal.ofReal (hi 1 - lo 1) *
          ENNReal.ofReal (hi 2 - lo 2) =
        ENNReal.ofReal (((hi 0 - lo 0) * (hi 1 - lo 1)) * (hi 2 - lo 2)) := by
      rw [h_step1]
      rw [ENNReal.ofReal_mul (mul_nonneg h_a h_b)] <;> ring
    rw [h6, h_dims]

  have h_main : volume (anisotropicRescalingMap g c d m '' E) ≤ volume box :=
    measure_mono h_image_sub
  rw [h_vol_box] at h_main
  exact h_main

end Kakeya.Assouad
