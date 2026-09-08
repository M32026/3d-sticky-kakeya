/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Trigonometric helpers

Consequences of Jordan's inequality `2φ/π ≤ sin φ`: for unit vectors in `ℝ³` whose first
coordinate is constrained by a cosine, and for the two-sided comparison between an arc
`arccos s` and the chord it subtends, together with the two facts about `sin` and the
unoriented vector angle that the chord-angle bound `Tube.norm_perp_direction_le_of_chord`
needs and Mathlib does not have.

## Blueprint correspondence

* `Real.sin_add_le_sin_add_sin` ↔ `lem:sinAddLe`;
* `InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle` ↔ `lem:normPerpEqSinAngle`.
-/

open scoped InnerProductSpace

@[expose] public section

/-- If `(a₀, a₁, a₂)` is a unit vector whose first coordinate satisfies `|a₀| ≤ cos φ` for some
`0 < φ ≤ π / 2`, then the remaining two coordinates cannot both be small:
`√2 · φ / π ≤ max |a₁| |a₂|`. -/
theorem sqrt_two_mul_div_pi_le_max_abs {a₀ a₁ a₂ φ : ℝ}
    (hsum : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = 1) (ha₀ : |a₀| ≤ Real.cos φ)
    (hφ_pos : 0 < φ) (hφ_le : φ ≤ Real.pi / 2) :
    Real.sqrt 2 * φ / Real.pi ≤ max |a₁| |a₂| := by
  have hnn : (0 : ℝ) ≤ 2 / Real.pi * φ :=
    mul_nonneg (div_nonneg zero_le_two Real.pi_pos.le) hφ_pos.le
  have hc : a₀ ^ 2 ≤ Real.cos φ ^ 2 := sq_le_sq' (neg_le_of_abs_le ha₀) (le_of_abs_le ha₀)
  have h₁ : (2 / Real.pi * φ) ^ 2 ≤ a₁ ^ 2 + a₂ ^ 2 :=
    (pow_le_pow_left₀ hnn (Real.mul_le_sin hφ_pos.le hφ_le) 2).trans <| by
      rw [Real.sin_sq]; linarith only [hsum, hc]
  have h₂ : a₁ ^ 2 + a₂ ^ 2 ≤ max |a₁| |a₂| ^ 2 + max |a₁| |a₂| ^ 2 :=
    add_le_add (sq_le_sq' (neg_le_of_abs_le (le_max_left _ _)) (le_of_abs_le (le_max_left _ _)))
      (sq_le_sq' (neg_le_of_abs_le (le_max_right _ _)) (le_of_abs_le (le_max_right _ _)))
  have h₃ : (Real.sqrt 2 * φ / Real.pi) ^ 2 * 2 = (2 / Real.pi * φ) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt zero_le_two]; ring
  exact le_of_sq_le_sq (le_of_mul_le_mul_right
    (h₃.trans_le ((h₁.trans h₂).trans_eq (mul_two _).symm)) two_pos)
    ((abs_nonneg a₁).trans (le_max_left _ _))

/-- **Sine is subadditive on a quarter turn** (blueprint `lem:sinAddLe`).

Mathlib has no `Real.sin_add_le`; the bound is needed at the point where the chord-angle
argument splits an angle into two nonnegative pieces. -/
theorem Real.sin_add_le_sin_add_sin {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x + y ≤ Real.pi / 2) :
    Real.sin (x + y) ≤ Real.sin x + Real.sin y := by
  have hsinx : 0 ≤ Real.sin x := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos.le])
  have hsiny : 0 ≤ Real.sin y := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi hy (by linarith [Real.pi_pos.le])
  rw [Real.sin_add]
  nlinarith [Real.cos_le_one x, Real.cos_le_one y, hsinx, hsiny]

/-- **The transverse part of a unit vector is the sine of the angle** (blueprint
`lem:normPerpEqSinAngle`).  For unit vectors `e`, `f`, the component of `f` orthogonal to `e`
has norm `sin ∠(e, f)`; this is the bridge between the transverse bookkeeping of tubes, which
is stated in norms, and the angle triangle inequality, which is stated in angles. -/
theorem InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {e f : F} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    ‖f - (inner ℝ e f : ℝ) • e‖ = Real.sin (InnerProductGeometry.angle e f) := by
  let a : ℝ := inner ℝ e f
  have hinner : ⟪e, f⟫_ℝ = a := rfl
  have hns : ‖a • e‖ ^ 2 = a ^ 2 * ‖e‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hsq1 : ‖f - a • e‖ ^ 2 = 1 - a ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm]
    rw [hinner, hns, he, hf]
    ring
  have hnsub : 0 ≤ 1 - a ^ 2 := by
    rw [← hsq1]
    exact sq_nonneg _
  have hrhs : √(⟪e, e⟫_ℝ * ⟪f, f⟫_ℝ - ⟪e, f⟫_ℝ * ⟪e, f⟫_ℝ) = √(1 - a ^ 2) := by
    congr 1
    rw [real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm, he, hf, hinner]
    ring
  have hsin : Real.sin (angle e f) = √(1 - a ^ 2) := by
    calc
      Real.sin (angle e f) = Real.sin (angle e f) * (1 * 1) := by norm_num
      _ = Real.sin (angle e f) * (‖e‖ * ‖f‖) := by rw [he, hf]
      _ = √(1 - a ^ 2) := by rw [sin_angle_mul_norm_mul_norm, hrhs]
  have hsq2 : Real.sin (angle e f) ^ 2 = 1 - a ^ 2 := by
    rw [hsin, Real.sq_sqrt hnsub]
  have hnonneg_r : 0 ≤ Real.sin (angle e f) := InnerProductGeometry.sin_angle_nonneg e f
  rw [← (sq_eq_sq₀ (norm_nonneg _) hnonneg_r)]
  exact hsq1.trans hsq2.symm

/-- **Chord below arc.**  If `d` is the chord `d² = 2 - 2s` subtended by the arc `arccos s`
(with `s ∈ [0,1]`), then `d ≤ arccos s`; this is `2 - 2 cos φ ≤ φ²`. -/
lemma chord_le_arccos {d s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hdsq : d ^ 2 = 2 - 2 * s) : d ≤ Real.arccos s := by
  have h := Real.one_sub_sq_div_two_le_cos (x := Real.arccos s)
  rw [Real.cos_arccos (by linarith) hs1] at h
  exact le_of_sq_le_sq (by linarith) (Real.arccos_nonneg s)

/-- **Arc below twice the chord.**  Converse of `chord_le_arccos`: the chord equals
`2 sin (φ/2)`, and Jordan's inequality `(2/π) x ≤ sin x` on `[0, π/2]` gives `φ ≤ 4 sin (φ/2)`. -/
lemma arccos_le_two_mul_chord {d s : ℝ} (hd : 0 ≤ d) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hdsq : d ^ 2 = 2 - 2 * s) : Real.arccos s ≤ 2 * d := by
  set φ := Real.arccos s with hφ
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg s
  have hφ2 : φ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr hs0
  have hsin : 0 ≤ Real.sin (φ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq : d ^ 2 = (2 * Real.sin (φ / 2)) ^ 2 := by
    have hhalf := Real.cos_two_mul_eq_one_sub (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring, Real.cos_arccos (by linarith) hs1] at hhalf
    linarith
  have hd_eq : d = 2 * Real.sin (φ / 2) := by
    have h := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq hd, Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 * Real.sin (φ / 2))] at h
  have hj : φ / Real.pi ≤ Real.sin (φ / 2) := by
    calc φ / Real.pi = 2 / Real.pi * (φ / 2) := by ring
      _ ≤ _ := Real.mul_le_sin (by linarith) (by linarith)
  rw [div_le_iff₀ Real.pi_pos] at hj
  rw [hd_eq]
  nlinarith [Real.pi_le_four]

/-- **Small transverse coordinates force a small angle.**  If the coordinate `t` of a unit vector
satisfies `t² ≥ 1 - 2k²` (its two other coordinates being at most `k`), then `arccos |t| ≤ 3k`:
`sin (arccos |t|) ≤ √2 k`, and `x ≤ (π/2) sin x` on `[0, π/2]` with `(π/2)√2 ≤ 3`. -/
lemma arccos_abs_le_three_mul {t k : ℝ} (hk : 0 ≤ k) (ht : |t| ≤ 1)
    (h : 1 - 2 * k ^ 2 ≤ t ^ 2) : Real.arccos |t| ≤ 3 * k := by
  set φ := Real.arccos |t| with hφ
  have hφ0 : 0 ≤ φ := Real.arccos_nonneg _
  have hφ2 : φ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (abs_nonneg t)
  have hcos : Real.cos φ = |t| := Real.cos_arccos (by linarith [abs_nonneg t]) ht
  have hsin0 : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [Real.pi_pos])
  have hsin_sq : Real.sin φ ^ 2 = 1 - t ^ 2 := by
    have hp := Real.sin_sq_add_cos_sq φ
    rw [hcos] at hp
    linarith [sq_abs t]
  have hsin_le : Real.sin φ ≤ Real.sqrt 2 * k := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2,
      mul_nonneg (Real.sqrt_nonneg 2) hk]
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hj : φ ≤ Real.pi / 2 * Real.sin φ := by
    have h8 := mul_le_mul_of_nonneg_left (Real.mul_le_sin hφ0 hφ2)
      (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    have h9 : Real.pi / 2 * (2 / Real.pi * φ) = φ := by field_simp
    linarith
  nlinarith [Real.pi_le_four]
