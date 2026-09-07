import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Direction bin restriction for Route B

Pigeonhole tube directions into narrow angular bins and restrict the family
to a selected bin.

## Key results

- `horizontalAngle`: angle of the horizontal direction component in [0, 2π)
- `horizontalAngle_cos`, `horizontalAngle_sin`: polar coordinate identities
- `direction_incidence_bound`: |inner(d, binPerpVector θ)| ≤ (√3/2)·|φ - θ|

## Whiteprint node

`PureWZ2/Grains/DirectionPigeonhole`
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set InnerProductGeometry Real

attribute [local instance] Classical.propDecidable

/-- Horizontal component of a Point3 as a Point2. -/
def horizontal2 (d : Point3) : Point2 :=
  WithLp.toLp 2 ![d 0, d 1]

/-- Norm squared of horizontal component. -/
lemma horizontal2_norm_sq (d : Point3) :
    ‖horizontal2 d‖^2 = (d 0)^2 + (d 1)^2 := by
  have h : ‖horizontal2 d‖^2 = ∑ i : Fin 2, ((horizontal2 d) i)^2 :=
    EuclideanSpace.real_norm_sq_eq (horizontal2 d)
  rw [h]
  have h2 : ∑ i : Fin 2, ((horizontal2 d) i)^2 = ((horizontal2 d) 0)^2 + ((horizontal2 d) 1)^2 := by
    simp [Fin.sum_univ_succ] <;> ring
  rw [h2]
  have h3 : (horizontal2 d) 0 = d 0 := by simp [horizontal2] <;> norm_num
  have h4 : (horizontal2 d) 1 = d 1 := by simp [horizontal2] <;> norm_num
  rw [h3, h4] <;> ring

/-- Full norm squared of a Point3. -/
private lemma point3_full_norm_sq (d : Point3) :
    ‖d‖^2 = (d 0)^2 + (d 1)^2 + (d 2)^2 := by
  have h : ‖d‖^2 = ∑ i : Fin 3, (d i)^2 := EuclideanSpace.real_norm_sq_eq d
  rw [h]
  have h2 : ∑ i : Fin 3, (d i)^2 = (d 0)^2 + (d 1)^2 + (d 2)^2 := by
    simp [Fin.sum_univ_succ] <;> ring
  exact h2

/-- Norm of the horizontal component ≤ √3/2 for line-class directions. -/
lemma horizontal_norm_le_sqrt3_2 {d : Point3} (hd : ‖d‖ = 1)
    (hvert : (1 / 2 : ℝ) ≤ |d 2|) : ‖horizontal2 d‖ ≤ Real.sqrt 3 / 2 := by
  have h1 : ‖d‖^2 = (d 0)^2 + (d 1)^2 + (d 2)^2 := point3_full_norm_sq d
  have h2 : (d 2)^2 ≥ 1 / 4 := by
    have h21 : |d 2| ≥ 1 / 2 := hvert
    have h22 : (d 2)^2 = |d 2|^2 := by rw [sq_abs]
    rw [h22]
    nlinarith
  have h3 : (d 0)^2 + (d 1)^2 ≤ 3 / 4 := by
    rw [hd] at h1; nlinarith
  have h4 : ‖horizontal2 d‖^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
  have h5 : (Real.sqrt 3 / 2)^2 = 3 / 4 := by
    have h6 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    field_simp [h6] <;> ring_nf <;> norm_num
  have h7 : ‖horizontal2 d‖^2 ≤ (Real.sqrt 3 / 2)^2 := by
    rw [h4, h5] <;> exact h3
  have hpos : 0 ≤ ‖horizontal2 d‖ := by positivity
  have hsqrt_pos : 0 ≤ Real.sqrt 3 / 2 := by positivity
  nlinarith

/-- If horizontal norm is zero, then d 0 = d 1 = 0. -/
lemma horizontal_norm_zero_eq {d : Point3} (hd : ‖d‖ = 1)
    (h : ‖horizontal2 d‖ = 0) : d 0 = 0 ∧ d 1 = 0 := by
  have h1 : ‖horizontal2 d‖^2 = 0 := by rw [h] <;> ring
  have h2 : (d 0)^2 + (d 1)^2 = 0 := by
    rw [horizontal2_norm_sq d] at h1; exact h1
  exact ⟨by nlinarith, by nlinarith⟩

/-- Horizontal angle in [0, 2π) using arccos. -/
def horizontalAngle (d : Point3) : ℝ :=
  let r := ‖horizontal2 d‖
  if r = 0 then 0
  else if d 1 ≥ 0 then Real.arccos (d 0 / r)
  else 2 * Real.pi - Real.arccos (d 0 / r)

/-- Cosine of the horizontal angle (requires nonzero horizontal component). -/
lemma horizontalAngle_cos {d : Point3} (hd : ‖d‖ = 1)
    (hr : ‖horizontal2 d‖ ≠ 0) :
    Real.cos (horizontalAngle d) = (d 0) / ‖horizontal2 d‖ := by
  let r := ‖horizontal2 d‖
  have hr_pos : 0 < r := by
    have h' : 0 ≤ r := by positivity
    exact lt_of_le_of_ne h' (Ne.symm hr)
  have h_d0_le_one : -1 ≤ d 0 / r ∧ d 0 / r ≤ 1 := by
    have h1 : (d 0)^2 ≤ r^2 := by
      have h2 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
      nlinarith
    have h3 : |d 0 / r| ≤ 1 := by
      calc |d 0 / r|
        = |d 0| / r := by rw [abs_div] <;> rw [abs_of_pos hr_pos]
      _ ≤ r / r := by gcongr <;> exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
      _ = 1 := by field_simp [hr_pos.ne']
    exact abs_le.mp h3
  dsimp only [horizontalAngle]
  rw [if_neg hr]
  by_cases h_y : d 1 ≥ 0
  · rw [if_pos h_y]
    exact Real.cos_arccos h_d0_le_one.1 h_d0_le_one.2
  · rw [if_neg h_y]
    have h_cos : Real.cos (2 * Real.pi - Real.arccos (d 0 / r)) = Real.cos (Real.arccos (d 0 / r)) := by
      rw [Real.cos_sub] <;> simp [Real.cos_two_pi, Real.sin_two_pi] <;> ring
    rw [h_cos]
    exact Real.cos_arccos h_d0_le_one.1 h_d0_le_one.2

/-- Sine of the horizontal angle (requires nonzero horizontal component). -/
lemma horizontalAngle_sin {d : Point3} (hd : ‖d‖ = 1)
    (hr : ‖horizontal2 d‖ ≠ 0) :
    Real.sin (horizontalAngle d) = (d 1) / ‖horizontal2 d‖ := by
  let r := ‖horizontal2 d‖
  have hr_pos : 0 < r := by
    have h' : 0 ≤ r := by positivity
    exact lt_of_le_of_ne h' (Ne.symm hr)
  have h_d0_le_one : -1 ≤ d 0 / r ∧ d 0 / r ≤ 1 := by
    have h1 : (d 0)^2 ≤ r^2 := by
      have h2 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
      nlinarith
    have h3 : |d 0 / r| ≤ 1 := by
      calc |d 0 / r|
        = |d 0| / r := by rw [abs_div] <;> rw [abs_of_pos hr_pos]
      _ ≤ r / r := by gcongr <;> exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
      _ = 1 := by field_simp [hr_pos.ne']
    exact abs_le.mp h3
  dsimp only [horizontalAngle]
  rw [if_neg hr]
  by_cases h_y : d 1 ≥ 0
  · rw [if_pos h_y]
    have h_sin : Real.sin (Real.arccos (d 0 / r)) = Real.sqrt (1 - (d 0 / r)^2) := Real.sin_arccos (d 0 / r)
    rw [h_sin]
    have h3 : 1 - (d 0 / r)^2 = (d 1 / r)^2 := by
      have h4 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
      field_simp [hr_pos.ne'] <;> nlinarith
    rw [h3]
    have h4 : 0 ≤ d 1 / r := by positivity
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h4]
  · have h_y' : d 1 < 0 := by linarith
    rw [if_neg h_y]
    have h_sin : Real.sin (2 * Real.pi - Real.arccos (d 0 / r)) = -Real.sin (Real.arccos (d 0 / r)) := by
      rw [Real.sin_sub] <;> simp [Real.cos_two_pi, Real.sin_two_pi] <;> ring
    rw [h_sin, Real.sin_arccos]
    have h3 : 1 - (d 0 / r)^2 = (d 1 / r)^2 := by
      have h4 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
      field_simp [hr_pos.ne'] <;> nlinarith
    rw [h3]
    have h4 : d 1 / r < 0 := div_neg_of_neg_of_pos h_y' hr_pos
    have h7 : Real.sqrt ((d 1 / r)^2) = |d 1 / r| := by rw [Real.sqrt_sq_eq_abs]
    rw [h7, abs_of_neg h4] <;> ring

/-- Unit vector perpendicular to the horizontal direction at angle `θ`. -/
def binPerpVector (θ : ℝ) : Point3 :=
  WithLp.toLp 2 ![ -Real.sin θ, Real.cos θ, 0 ]

/-- `binPerpVector θ` has norm 1. -/
lemma binPerpVector_norm (θ : ℝ) : ‖binPerpVector θ‖ = 1 := by
  let v : Fin 3 → ℝ := ![ -Real.sin θ, Real.cos θ, 0 ]
  have h1 : ‖binPerpVector θ‖^2 = ∑ i : Fin 3, (v i)^2 :=
    EuclideanSpace.real_norm_sq_eq (binPerpVector θ)
  have h2 : ∑ i : Fin 3, (v i)^2 = (Real.sin θ)^2 + (Real.cos θ)^2 := by
    simp [v, Fin.sum_univ_succ] <;> ring
  have h3 : ‖binPerpVector θ‖^2 = 1 := by
    rw [h1, h2]
    have h4 : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h4] <;> norm_num
  have hpos : 0 ≤ ‖binPerpVector θ‖ := by positivity
  nlinarith

/-- Direction incidence bound via angle difference.

For a line-class direction `d` with horizontal angle `φ`,
`|inner(d, binPerpVector θ)| ≤ ‖horizontal2 d‖ * |φ - θ| ≤ (√3/2) * |φ - θ|`. -/
lemma direction_incidence_bound
    {d : Point3} (hd : ‖d‖ = 1) (hvert : (1 / 2 : ℝ) ≤ |d 2|)
    {θ : ℝ} :
    |inner ℝ d (binPerpVector θ)| ≤
      (Real.sqrt 3 / 2) * |horizontalAngle d - θ| := by
  let r : ℝ := ‖horizontal2 d‖
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_le : r ≤ Real.sqrt 3 / 2 := horizontal_norm_le_sqrt3_2 hd hvert
  by_cases hr : r = 0
  · -- Horizontal component zero: incidence is zero
    have h0 : d 0 = 0 ∧ d 1 = 0 := horizontal_norm_zero_eq hd hr
    have hbp0 : (binPerpVector θ) 0 = -Real.sin θ := by simp [binPerpVector] <;> norm_num
    have hbp1 : (binPerpVector θ) 1 = Real.cos θ := by simp [binPerpVector] <;> norm_num
    have hbp2 : (binPerpVector θ) 2 = 0 := by simp [binPerpVector] <;> norm_num
    have h_inner : inner ℝ d (binPerpVector θ) = 0 := by
      have h_sum : inner ℝ d (binPerpVector θ) = ∑ i : Fin 3, d i * (binPerpVector θ) i := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp <;> ring
      rw [h_sum]
      have h_fin : ∑ i : Fin 3, d i * (binPerpVector θ) i =
          d 0 * (binPerpVector θ) 0 + d 1 * (binPerpVector θ) 1 + d 2 * (binPerpVector θ) 2 := by
        simp [Fin.sum_univ_succ] <;> ring
      rw [h_fin, h0.1, h0.2, hbp0, hbp1, hbp2] <;> ring
    rw [h_inner, abs_zero]
    exact mul_nonneg (by positivity) (by positivity)
  · -- Horizontal component nonzero
    have hr_pos : 0 < r := by
      have h' : 0 ≤ r := by positivity
      exact lt_of_le_of_ne h' (Ne.symm hr)
    have h_cos : Real.cos (horizontalAngle d) = d 0 / r := horizontalAngle_cos hd hr
    have h_sin : Real.sin (horizontalAngle d) = d 1 / r := horizontalAngle_sin hd hr
    have hbp0 : (binPerpVector θ) 0 = -Real.sin θ := by simp [binPerpVector] <;> norm_num
    have hbp1 : (binPerpVector θ) 1 = Real.cos θ := by simp [binPerpVector] <;> norm_num
    have hbp2 : (binPerpVector θ) 2 = 0 := by simp [binPerpVector] <;> norm_num
    have h_inner : inner ℝ d (binPerpVector θ) = r * Real.sin (horizontalAngle d - θ) := by
      have h_sum : inner ℝ d (binPerpVector θ) = ∑ i : Fin 3, d i * (binPerpVector θ) i := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp <;> ring
      have h1 : inner ℝ d (binPerpVector θ) =
          (d 0) * (-(Real.sin θ)) + (d 1) * (Real.cos θ) := by
        rw [h_sum]
        have h_fin : ∑ i : Fin 3, d i * (binPerpVector θ) i =
            d 0 * (binPerpVector θ) 0 + d 1 * (binPerpVector θ) 1 + d 2 * (binPerpVector θ) 2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h_fin, hbp0, hbp1, hbp2] <;> ring
      rw [h1]
      have h2 : d 0 = r * Real.cos (horizontalAngle d) := by
        rw [h_cos] <;> field_simp [hr_pos.ne'] <;> ring
      have h3 : d 1 = r * Real.sin (horizontalAngle d) := by
        rw [h_sin] <;> field_simp [hr_pos.ne'] <;> ring
      rw [h2, h3]
      rw [Real.sin_sub] <;> ring
    rw [h_inner]
    have h4 : |r * Real.sin (horizontalAngle d - θ)| = r * |Real.sin (horizontalAngle d - θ)| := by
      rw [abs_mul, abs_of_nonneg hr_nonneg]
    rw [h4]
    have h5 : |Real.sin (horizontalAngle d - θ)| ≤ |horizontalAngle d - θ| := by
      exact abs_sin_le_abs
    have h6 : r * |Real.sin (horizontalAngle d - θ)| ≤ r * |horizontalAngle d - θ| := by gcongr
    have h7 : r * |horizontalAngle d - θ| ≤ (Real.sqrt 3 / 2) * |horizontalAngle d - θ| := by
      gcongr <;> exact abs_nonneg _
    exact h6.trans h7

/-- horizontalAngle lies in [0, 2π). -/
lemma horizontalAngle_range {d : Point3} (hd : ‖d‖ = 1) :
    0 ≤ horizontalAngle d ∧ horizontalAngle d < 2 * Real.pi := by
  let r := ‖horizontal2 d‖
  by_cases hr : r = 0
  · have h_angle : horizontalAngle d = 0 := by
      dsimp only [horizontalAngle]; rw [if_pos hr]
    rw [h_angle]
    exact ⟨by norm_num, by linarith [Real.pi_pos]⟩
  · have hr_pos : 0 < r := by
      have h' : 0 ≤ r := by positivity
      exact lt_of_le_of_ne h' (Ne.symm hr)
    have h_d0_le_one : -1 ≤ d 0 / r ∧ d 0 / r ≤ 1 := by
      have h1 : (d 0)^2 ≤ r^2 := by
        have h2 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
        nlinarith
      have h3 : |d 0 / r| ≤ 1 := by
        calc |d 0 / r|
          = |d 0| / r := by rw [abs_div] <;> rw [abs_of_pos hr_pos]
        _ ≤ r / r := by gcongr <;> exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
        _ = 1 := by field_simp [hr_pos.ne']
      exact abs_le.mp h3
    dsimp only [horizontalAngle]
    rw [if_neg hr]
    by_cases h_y : d 1 ≥ 0
    · rw [if_pos h_y]
      have h1 : 0 ≤ Real.arccos (d 0 / r) := Real.arccos_nonneg _
      have h2 : Real.arccos (d 0 / r) ≤ Real.pi := Real.arccos_le_pi _
      exact ⟨h1, by linarith [Real.pi_pos]⟩
    · have h_y' : d 1 < 0 := by linarith
      rw [if_neg h_y]
      have h_r2_pos : 0 < r^2 := by exact sq_pos_of_pos hr_pos
      have h_d0_lt_one : d 0 / r < 1 := by
        have h1 : (d 0 / r)^2 < 1 := by
          have h2 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
          have h3 : (d 0 / r)^2 = (d 0)^2 / r^2 := by
            field_simp [hr_pos.ne'] <;> ring
          rw [h3, div_lt_one h_r2_pos]; nlinarith
        nlinarith [abs_nonneg (d 0 / r)]
      have h1 : 0 < Real.arccos (d 0 / r) := Real.arccos_pos.mpr h_d0_lt_one
      have h2 : Real.arccos (d 0 / r) ≤ Real.pi := Real.arccos_le_pi _
      constructor
      · linarith [Real.pi_pos]
      · linarith [Real.pi_pos]

/-- Direction incidence bound via angle difference (absolute-value vertical condition).

Like `direction_incidence_bound`, but accepts `1/2 ≤ |d 2|` instead of `1/2 ≤ d 2`.
The cosine/sine identities for `horizontalAngle` do not depend on the sign of `d 2`,
and the horizontal norm bound only needs `(d 2)^2 ≥ 1/4`. -/
lemma direction_incidence_bound_abs
    {d : Point3} (hd : ‖d‖ = 1) (hvert_abs : (1 / 2 : ℝ) ≤ |d 2|)
    {θ : ℝ} :
    |inner ℝ d (binPerpVector θ)| ≤
      (Real.sqrt 3 / 2) * |horizontalAngle d - θ| := by
  let r : ℝ := ‖horizontal2 d‖
  have hr_nonneg : 0 ≤ r := by positivity
  have hr_le : r ≤ Real.sqrt 3 / 2 := by
    have h1 : ‖d‖^2 = (d 0)^2 + (d 1)^2 + (d 2)^2 := point3_full_norm_sq d
    have h2 : (d 2)^2 ≥ 1 / 4 := by
      have h21 : (d 2)^2 = |d 2|^2 := by rw [sq_abs]
      rw [h21]; nlinarith [hvert_abs]
    have h3 : (d 0)^2 + (d 1)^2 ≤ 3 / 4 := by rw [hd] at h1; nlinarith
    have h4 : ‖horizontal2 d‖^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  by_cases hr : r = 0
  · have h0 : d 0 = 0 ∧ d 1 = 0 := horizontal_norm_zero_eq hd hr
    have h_inner : inner ℝ d (binPerpVector θ) = 0 := by
      have h_sum : inner ℝ d (binPerpVector θ) = ∑ i : Fin 3, d i * (binPerpVector θ) i := by
        rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intro i _; simp <;> ring
      rw [h_sum]
      have h_fin : ∑ i : Fin 3, d i * (binPerpVector θ) i =
          d 0 * (binPerpVector θ) 0 + d 1 * (binPerpVector θ) 1 + d 2 * (binPerpVector θ) 2 := by
        simp [Fin.sum_univ_succ] <;> ring
      rw [h_fin, h0.1, h0.2]
      have hbp2 : (binPerpVector θ) 2 = 0 := by simp [binPerpVector] <;> norm_num
      rw [hbp2] <;> ring
    rw [h_inner, abs_zero]
    exact mul_nonneg (by positivity) (by positivity)
  · have hr_pos : 0 < r := by
      have h' : 0 ≤ r := by positivity
      exact lt_of_le_of_ne h' (Ne.symm hr)
    have h_d0_le_one : -1 ≤ d 0 / r ∧ d 0 / r ≤ 1 := by
      have h1 : (d 0)^2 ≤ r^2 := by
        have h2 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
        nlinarith
      have h3 : |d 0 / r| ≤ 1 := by
        calc |d 0 / r|
          = |d 0| / r := by rw [abs_div] <;> rw [abs_of_pos hr_pos]
        _ ≤ r / r := by gcongr <;> exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
        _ = 1 := by field_simp [hr_pos.ne']
      exact abs_le.mp h3
    have h_cos : Real.cos (horizontalAngle d) = d 0 / r := by
      dsimp only [horizontalAngle]
      rw [if_neg hr]
      by_cases h_y : d 1 ≥ 0
      · rw [if_pos h_y]; exact Real.cos_arccos h_d0_le_one.1 h_d0_le_one.2
      · rw [if_neg h_y]
        have h_cos2 : Real.cos (2 * Real.pi - Real.arccos (d 0 / r)) = Real.cos (Real.arccos (d 0 / r)) := by
          rw [Real.cos_sub] <;> simp [Real.cos_two_pi, Real.sin_two_pi] <;> ring
        rw [h_cos2]; exact Real.cos_arccos h_d0_le_one.1 h_d0_le_one.2
    have h_sin : Real.sin (horizontalAngle d) = d 1 / r := by
      dsimp only [horizontalAngle]
      rw [if_neg hr]
      by_cases h_y : d 1 ≥ 0
      · rw [if_pos h_y]
        have h_sin2 : Real.sin (Real.arccos (d 0 / r)) = Real.sqrt (1 - (d 0 / r)^2) := Real.sin_arccos (d 0 / r)
        rw [h_sin2]
        have h3 : 1 - (d 0 / r)^2 = (d 1 / r)^2 := by
          have h4 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
          field_simp [hr_pos.ne'] <;> nlinarith
        rw [h3]
        have h4 : 0 ≤ d 1 / r := by positivity
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h4]
      · have h_y' : d 1 < 0 := by linarith
        rw [if_neg h_y]
        have h_sin2 : Real.sin (2 * Real.pi - Real.arccos (d 0 / r)) = -Real.sin (Real.arccos (d 0 / r)) := by
          rw [Real.sin_sub] <;> simp [Real.cos_two_pi, Real.sin_two_pi] <;> ring
        rw [h_sin2, Real.sin_arccos]
        have h3 : 1 - (d 0 / r)^2 = (d 1 / r)^2 := by
          have h4 : r^2 = (d 0)^2 + (d 1)^2 := horizontal2_norm_sq d
          field_simp [hr_pos.ne'] <;> nlinarith
        rw [h3]
        have h4 : d 1 / r < 0 := div_neg_of_neg_of_pos h_y' hr_pos
        have h7 : Real.sqrt ((d 1 / r)^2) = |d 1 / r| := by rw [Real.sqrt_sq_eq_abs]
        rw [h7, abs_of_neg h4] <;> ring
    have hbp0 : (binPerpVector θ) 0 = -Real.sin θ := by simp [binPerpVector] <;> norm_num
    have hbp1 : (binPerpVector θ) 1 = Real.cos θ := by simp [binPerpVector] <;> norm_num
    have hbp2 : (binPerpVector θ) 2 = 0 := by simp [binPerpVector] <;> norm_num
    have h_inner : inner ℝ d (binPerpVector θ) = r * Real.sin (horizontalAngle d - θ) := by
      have h_sum : inner ℝ d (binPerpVector θ) = ∑ i : Fin 3, d i * (binPerpVector θ) i := by
        rw [PiLp.inner_apply]; apply Finset.sum_congr rfl; intro i _; simp <;> ring
      have h1 : inner ℝ d (binPerpVector θ) = (d 0) * (-(Real.sin θ)) + (d 1) * (Real.cos θ) := by
        rw [h_sum]
        have h_fin : ∑ i : Fin 3, d i * (binPerpVector θ) i =
            d 0 * (binPerpVector θ) 0 + d 1 * (binPerpVector θ) 1 + d 2 * (binPerpVector θ) 2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h_fin, hbp0, hbp1, hbp2] <;> ring
      rw [h1]
      have h2 : d 0 = r * Real.cos (horizontalAngle d) := by rw [h_cos] <;> field_simp [hr_pos.ne'] <;> ring
      have h3 : d 1 = r * Real.sin (horizontalAngle d) := by rw [h_sin] <;> field_simp [hr_pos.ne'] <;> ring
      rw [h2, h3, Real.sin_sub] <;> ring
    rw [h_inner]
    have h4 : |r * Real.sin (horizontalAngle d - θ)| = r * |Real.sin (horizontalAngle d - θ)| := by
      rw [abs_mul, abs_of_nonneg hr_nonneg]
    rw [h4]
    have h5 : |Real.sin (horizontalAngle d - θ)| ≤ |horizontalAngle d - θ| := by
      exact abs_sin_le_abs
    have h6 : r * |Real.sin (horizontalAngle d - θ)| ≤ r * |horizontalAngle d - θ| := by gcongr
    have h7 : r * |horizontalAngle d - θ| ≤ (Real.sqrt 3 / 2) * |horizontalAngle d - θ| := by
      gcongr <;> exact abs_nonneg _
    exact h6.trans h7

/-- Weighted pigeonhole: some color class has at least 1/N of total weight. -/
lemma weighted_pigeonhole_simple {n N : ℕ} (hN_pos : 0 < N)
    (weight : Fin n → ENNReal) (color : Fin n → Fin N) :
    ∃ k : Fin N,
      (∑ i, weight i) ≤ (N : ENNReal) * ∑ i ∈ (Finset.univ.filter fun i => color i = k), weight i := by
  let classWeight : Fin N → ENNReal := fun k =>
    ∑ i ∈ (Finset.univ.filter fun i => color i = k), weight i
  have htotal : (∑ i, weight i) = ∑ k : Fin N, classWeight k := by
    calc
      (∑ i, weight i)
        = ∑ i : Fin n, ∑ k : Fin N, if color i = k then weight i else 0 := by
          apply Finset.sum_congr rfl; intro i _
          have h : (∑ k : Fin N, if color i = k then weight i else 0) = weight i := by
            rw [Finset.sum_eq_single_of_mem (color i) (Finset.mem_univ _)]
            · rw [if_pos rfl]
            · intro j _ hne; rw [if_neg hne.symm]
          exact h.symm
      _ = ∑ k : Fin N, classWeight k := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          have h_eq : ∑ i : Fin n, (if color i = k then weight i else 0) =
              ∑ i ∈ (Finset.univ.filter fun i => color i = k), weight i := by
            rw [Finset.sum_ite] <;> simp
          exact h_eq
  have h_univ_nonempty : (Finset.univ : Finset (Fin N)).Nonempty := by
    refine ⟨⟨0, hN_pos⟩, by simp⟩
  rcases Finset.exists_max_image (Finset.univ : Finset (Fin N)) classWeight h_univ_nonempty with
    ⟨k, _, hk⟩
  refine ⟨k, ?_⟩
  calc
    (∑ i, weight i) = ∑ j : Fin N, classWeight j := htotal
    _ ≤ ∑ _j : Fin N, classWeight k := by
      apply Finset.sum_le_sum; intro j _; exact hk j (Finset.mem_univ j)
    _ = (N : ENNReal) * classWeight k := by simp

end Kakeya.Assouad

end
