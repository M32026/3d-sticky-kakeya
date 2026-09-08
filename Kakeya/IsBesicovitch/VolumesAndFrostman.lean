/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib
public import Kakeya.IsBesicovitch.PiTransfer
public import Kakeya.Shading

/-!
# Volume and Frostman estimates for the Besicovitch construction

This file proves the spherical Frostman estimate and the segment- and ball-thickening
volume bounds used by the Besicovitch-set assembly. It includes Euclidean wrappers for
the corresponding sup-norm estimates.
-/

@[expose] public section

open scoped ENNReal NNReal MeasureTheory Topology Pointwise

namespace Kakeya.IsBesicovitch

/-- The union of shades has volume at most `Jcard * δ^3`: every shade lies in
the same outer set `E'`, whose volume satisfies this bound. -/
theorem B10_containment
    {δ Jcard : ℝ} (_hδ_pos : 0 < δ)
    {Ω : Finset (EuclideanSpace ℝ (Fin 3))}
    (T : (ω : EuclideanSpace ℝ (Fin 3)) → ω ∈ Ω →
            ShadedTube δ.toNNReal (EuclideanSpace ℝ (Fin 3)))
    {E' : Set (EuclideanSpace ℝ (Fin 3))}
    (hE'_finite : MeasureTheory.volume E' ≠ ∞)
    (hshade_sub : ∀ ω (hω : ω ∈ Ω), (T ω hω).shade ⊆ E')
    (hE'_vol : MeasureTheory.volume.real E' ≤ Jcard * δ ^ 3) :
    MeasureTheory.volume.real (⋃ ω : Ω.attach, (T ω.val.val ω.val.property).shade) ≤
      Jcard * δ ^ 3 := by
  have hsub : (⋃ ω : Ω.attach, (T ω.val.val ω.val.property).shade) ⊆ E' := by
    apply Set.iUnion_subset
    intro ω
    exact hshade_sub ω.val.val ω.val.property
  have hmono : MeasureTheory.volume (⋃ ω : Ω.attach, (T ω.val.val ω.val.property).shade) ≤
      MeasureTheory.volume E' :=
    MeasureTheory.measure_mono hsub
  have htoReal :
      (MeasureTheory.volume (⋃ ω : Ω.attach, (T ω.val.val ω.val.property).shade)).toReal ≤
        (MeasureTheory.volume E').toReal :=
    ENNReal.toReal_mono hE'_finite hmono
  exact le_trans htoReal hE'_vol

/-- Key trigonometric identity used in the polar parametrization Lipschitz bound:
`(sin a - sin b)² + (cos a - cos b)² = 2 - 2 cos(a - b) ≤ (a - b)²`. -/
private lemma sphCap_sin_cos_diff_sq_le (a b : ℝ) :
    (Real.sin a - Real.sin b) ^ 2 + (Real.cos a - Real.cos b) ^ 2 ≤ (a - b) ^ 2 := by
  have h1 : (Real.sin a - Real.sin b) ^ 2 + (Real.cos a - Real.cos b) ^ 2
      = 2 - 2 * Real.cos (a - b) := by
    have hsa : Real.sin a ^ 2 + Real.cos a ^ 2 = 1 := Real.sin_sq_add_cos_sq a
    have hsb : Real.sin b ^ 2 + Real.cos b ^ 2 = 1 := Real.sin_sq_add_cos_sq b
    have hcab : Real.cos (a - b) = Real.cos a * Real.cos b + Real.sin a * Real.sin b :=
      Real.cos_sub a b
    nlinarith [hsa, hsb, hcab]
  rw [h1]
  have h2 : 1 - (a - b) ^ 2 / 2 ≤ Real.cos (a - b) :=
    Real.one_sub_sq_div_two_le_cos
  linarith

/-- The polar parametrization `g(θ, φ) = (sin θ cos φ, sin θ sin φ, cos θ)`
maps the rectangle `[0, π] × [0, 2π]` onto the unit sphere in 3-space. -/
private noncomputable def sphCap_polar (p : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (fun i => match i with
      | 0 => Real.sin (p 0) * Real.cos (p 1)
      | 1 => Real.sin (p 0) * Real.sin (p 1)
      | 2 => Real.cos (p 0))

private lemma sphCap_polar_apply_zero (p : Fin 2 → ℝ) :
    sphCap_polar p 0 = Real.sin (p 0) * Real.cos (p 1) := by
  simp [sphCap_polar, EuclideanSpace.equiv]

private lemma sphCap_polar_apply_one (p : Fin 2 → ℝ) :
    sphCap_polar p 1 = Real.sin (p 0) * Real.sin (p 1) := by
  simp [sphCap_polar, EuclideanSpace.equiv]

private lemma sphCap_polar_apply_two (p : Fin 2 → ℝ) :
    sphCap_polar p 2 = Real.cos (p 0) := by
  simp [sphCap_polar, EuclideanSpace.equiv]

/-- Auxiliary: bound on each Euclidean component, in terms of θ-diff and φ-diff. -/
private lemma sphCap_polar_dist_le (p q : Fin 2 → ℝ) :
    dist (sphCap_polar p) (sphCap_polar q) ≤ |p 0 - q 0| + |p 1 - q 1| := by
  set θ₁ := p 0
  set θ₂ := q 0
  set φ₁ := p 1
  set φ₂ := q 1
  set p' : Fin 2 → ℝ := ![θ₂, φ₁]
  have hp'0 : p' 0 = θ₂ := rfl
  have hp'1 : p' 1 = φ₁ := rfl
  have h_tri := dist_triangle (sphCap_polar p) (sphCap_polar p') (sphCap_polar q)
  have h_a : dist (sphCap_polar p) (sphCap_polar p') ≤ |θ₁ - θ₂| := by
    rw [EuclideanSpace.dist_eq]
    have h0 : dist (sphCap_polar p 0) (sphCap_polar p' 0) ^ 2 =
        (Real.sin θ₁ - Real.sin θ₂) ^ 2 * Real.cos φ₁ ^ 2 := by
      rw [Real.dist_eq, sphCap_polar_apply_zero, sphCap_polar_apply_zero, hp'0, hp'1]
      ring_nf
      rw [sq_abs]
      ring
    have h1 : dist (sphCap_polar p 1) (sphCap_polar p' 1) ^ 2 =
        (Real.sin θ₁ - Real.sin θ₂) ^ 2 * Real.sin φ₁ ^ 2 := by
      rw [Real.dist_eq, sphCap_polar_apply_one, sphCap_polar_apply_one, hp'0, hp'1]
      ring_nf
      rw [sq_abs]
      ring
    have h2 : dist (sphCap_polar p 2) (sphCap_polar p' 2) ^ 2 =
        (Real.cos θ₁ - Real.cos θ₂) ^ 2 := by
      rw [Real.dist_eq, sphCap_polar_apply_two, sphCap_polar_apply_two, hp'0]
      rw [sq_abs]
    have h_sum : ∑ i, dist (sphCap_polar p i) (sphCap_polar p' i) ^ 2 =
        (Real.sin θ₁ - Real.sin θ₂) ^ 2 + (Real.cos θ₁ - Real.cos θ₂) ^ 2 := by
      rw [Fin.sum_univ_three]
      rw [h0, h1, h2]
      have hpf : Real.cos φ₁ ^ 2 + Real.sin φ₁ ^ 2 = 1 := by
        rw [add_comm]; exact Real.sin_sq_add_cos_sq φ₁
      nlinarith [hpf]
    rw [h_sum]
    have h_key : (Real.sin θ₁ - Real.sin θ₂) ^ 2 + (Real.cos θ₁ - Real.cos θ₂) ^ 2
        ≤ (θ₁ - θ₂) ^ 2 := sphCap_sin_cos_diff_sq_le θ₁ θ₂
    have h_abs : (θ₁ - θ₂) ^ 2 = |θ₁ - θ₂| ^ 2 := (sq_abs _).symm
    rw [h_abs] at h_key
    exact Real.sqrt_le_sqrt h_key |>.trans_eq (Real.sqrt_sq (abs_nonneg _))
  have h_b : dist (sphCap_polar p') (sphCap_polar q) ≤ |φ₁ - φ₂| := by
    rw [EuclideanSpace.dist_eq]
    have h0 : dist (sphCap_polar p' 0) (sphCap_polar q 0) ^ 2 =
        Real.sin θ₂ ^ 2 * (Real.cos φ₁ - Real.cos φ₂) ^ 2 := by
      rw [Real.dist_eq, sphCap_polar_apply_zero, sphCap_polar_apply_zero, hp'0, hp'1]
      ring_nf
      rw [sq_abs]
      ring
    have h1 : dist (sphCap_polar p' 1) (sphCap_polar q 1) ^ 2 =
        Real.sin θ₂ ^ 2 * (Real.sin φ₁ - Real.sin φ₂) ^ 2 := by
      rw [Real.dist_eq, sphCap_polar_apply_one, sphCap_polar_apply_one, hp'0, hp'1]
      ring_nf
      rw [sq_abs]
      ring
    have h2 : dist (sphCap_polar p' 2) (sphCap_polar q 2) ^ 2 = 0 := by
      rw [Real.dist_eq, sphCap_polar_apply_two, sphCap_polar_apply_two, hp'0]
      change |Real.cos (q 0) - Real.cos (q 0)| ^ 2 = 0
      simp
    have h_sum : ∑ i, dist (sphCap_polar p' i) (sphCap_polar q i) ^ 2 =
        Real.sin θ₂ ^ 2 *
          ((Real.cos φ₁ - Real.cos φ₂) ^ 2 + (Real.sin φ₁ - Real.sin φ₂) ^ 2) := by
      rw [Fin.sum_univ_three]
      rw [h0, h1, h2]
      ring
    rw [h_sum]
    have h_key : (Real.sin φ₁ - Real.sin φ₂) ^ 2 + (Real.cos φ₁ - Real.cos φ₂) ^ 2
        ≤ (φ₁ - φ₂) ^ 2 := sphCap_sin_cos_diff_sq_le φ₁ φ₂
    have h_sin_le : Real.sin θ₂ ^ 2 ≤ 1 := by
      have h_abs : |Real.sin θ₂| ≤ 1 := Real.abs_sin_le_one θ₂
      have h_sq : Real.sin θ₂ ^ 2 = |Real.sin θ₂| ^ 2 := (sq_abs _).symm
      rw [h_sq]
      nlinarith [h_abs, abs_nonneg (Real.sin θ₂)]
    have h_total : Real.sin θ₂ ^ 2 *
          ((Real.cos φ₁ - Real.cos φ₂) ^ 2 + (Real.sin φ₁ - Real.sin φ₂) ^ 2) ≤
        (φ₁ - φ₂) ^ 2 := by
      have h_re : (Real.cos φ₁ - Real.cos φ₂) ^ 2 + (Real.sin φ₁ - Real.sin φ₂) ^ 2 =
          (Real.sin φ₁ - Real.sin φ₂) ^ 2 + (Real.cos φ₁ - Real.cos φ₂) ^ 2 := by ring
      rw [h_re]
      calc Real.sin θ₂ ^ 2 *
              ((Real.sin φ₁ - Real.sin φ₂) ^ 2 + (Real.cos φ₁ - Real.cos φ₂) ^ 2)
            ≤ 1 *
              ((Real.sin φ₁ - Real.sin φ₂) ^ 2 + (Real.cos φ₁ - Real.cos φ₂) ^ 2) := by
              apply mul_le_mul_of_nonneg_right h_sin_le
              positivity
        _ = (Real.sin φ₁ - Real.sin φ₂) ^ 2 + (Real.cos φ₁ - Real.cos φ₂) ^ 2 := one_mul _
        _ ≤ (φ₁ - φ₂) ^ 2 := h_key
    have h_abs : (φ₁ - φ₂) ^ 2 = |φ₁ - φ₂| ^ 2 := (sq_abs _).symm
    rw [h_abs] at h_total
    exact Real.sqrt_le_sqrt h_total |>.trans_eq (Real.sqrt_sq (abs_nonneg _))
  linarith

/-- The polar parametrization is `2`-Lipschitz from `Fin 2 → ℝ` (sup metric)
to `EuclideanSpace ℝ (Fin 3)` (L² metric). -/
private lemma sphCap_polar_lipschitz : LipschitzWith 2 sphCap_polar := by
  refine LipschitzWith.of_dist_le_mul (fun p q => ?_)
  have h := sphCap_polar_dist_le p q
  have h0 : |p 0 - q 0| ≤ dist p q := by
    have := dist_le_pi_dist p q 0
    rwa [Real.dist_eq] at this
  have h1 : |p 1 - q 1| ≤ dist p q := by
    have := dist_le_pi_dist p q 1
    rwa [Real.dist_eq] at this
  have hcoe : ((2 : ℝ≥0) : ℝ) = 2 := by norm_num
  rw [hcoe]
  linarith

/-- The "rectangle" `[0, π] × [0, 2π]` in `Fin 2 → ℝ`, expressed as `Set.Icc`. -/
private noncomputable def sphCap_rect : Set (Fin 2 → ℝ) :=
  Set.Icc (![0, 0] : Fin 2 → ℝ) (![Real.pi, 2 * Real.pi] : Fin 2 → ℝ)

private lemma sphCap_rect_mem_iff (p : Fin 2 → ℝ) :
    p ∈ sphCap_rect ↔ 0 ≤ p 0 ∧ p 0 ≤ Real.pi ∧ 0 ≤ p 1 ∧ p 1 ≤ 2 * Real.pi := by
  unfold sphCap_rect
  rw [Set.mem_Icc]
  constructor
  · rintro ⟨h_lo, h_hi⟩
    refine ⟨h_lo 0, h_hi 0, h_lo 1, h_hi 1⟩
  · rintro ⟨h00, h0pi, h10, h12pi⟩
    refine ⟨?_, ?_⟩
    · intro i; fin_cases i <;> simpa
    · intro i; fin_cases i <;> simpa

/-- The image of `sphCap_polar` on the rectangle `[0, π] × [0, 2π]` covers
the unit sphere in `EuclideanSpace ℝ (Fin 3)`. -/
private lemma sphCap_polar_surj_unit_sphere :
    {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} ⊆ sphCap_polar '' sphCap_rect := by
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  have hv_sq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    have hnorm_sq : ‖v‖ ^ 2 = 1 := by rw [hv]; ring
    rw [EuclideanSpace.norm_eq] at hnorm_sq
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at hnorm_sq
    rw [Fin.sum_univ_three] at hnorm_sq
    have h0 : ‖v 0‖ ^ 2 = v 0 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    have h1 : ‖v 1‖ ^ 2 = v 1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    have h2 : ‖v 2‖ ^ 2 = v 2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    rw [h0, h1, h2] at hnorm_sq
    exact hnorm_sq
  have hv2_le : v 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hv2_lb : -1 ≤ v 2 := by nlinarith [sq_nonneg (v 2 - (-1)), sq_nonneg (v 2 + 1), hv2_le]
  have hv2_ub : v 2 ≤ 1 := by nlinarith [sq_nonneg (v 2 - 1), sq_nonneg (v 2 + 1), hv2_le]
  set θ : ℝ := Real.arccos (v 2) with hθ_def
  have hθ_nn : 0 ≤ θ := Real.arccos_nonneg _
  have hθ_le : θ ≤ Real.pi := Real.arccos_le_pi _
  have hcosθ : Real.cos θ = v 2 := Real.cos_arccos hv2_lb hv2_ub
  have hsinθ_nn : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ_nn hθ_le
  have hsinθ_sq : Real.sin θ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [hcosθ] at hpyth
    linarith
  by_cases hsinθ_zero : Real.sin θ = 0
  · have hv0 : v 0 = 0 ∧ v 1 = 0 := by
      have h_sum : v 0 ^ 2 + v 1 ^ 2 = 0 := by rw [← hsinθ_sq, hsinθ_zero]; ring
      have h_v0sq : v 0 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h_v1sq : v 1 ^ 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_v0sq,
             pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h_v1sq⟩
    refine ⟨![θ, 0], ?_, ?_⟩
    · rw [sphCap_rect_mem_iff]
      refine ⟨hθ_nn, hθ_le, le_refl _, by positivity⟩
    · apply PiLp.ext
      intro i
      fin_cases i
      · change sphCap_polar ![θ, 0] 0 = v 0
        rw [sphCap_polar_apply_zero]
        change Real.sin (![θ, 0] 0 : ℝ) * Real.cos (![θ, 0] 1 : ℝ) = v 0
        simp [hsinθ_zero, hv0.1]
      · change sphCap_polar ![θ, 0] 1 = v 1
        rw [sphCap_polar_apply_one]
        change Real.sin (![θ, 0] 0 : ℝ) * Real.sin (![θ, 0] 1 : ℝ) = v 1
        simp [hsinθ_zero, hv0.2]
      · change sphCap_polar ![θ, 0] 2 = v 2
        rw [sphCap_polar_apply_two]
        change Real.cos (![θ, 0] 0 : ℝ) = v 2
        simp [hcosθ]
  · have hsinθ_pos : 0 < Real.sin θ := lt_of_le_of_ne hsinθ_nn (Ne.symm hsinθ_zero)
    set a : ℝ := v 0 / Real.sin θ with ha_def
    set b : ℝ := v 1 / Real.sin θ with hb_def
    have hab_sq : a ^ 2 + b ^ 2 = 1 := by
      have hsin_ne : Real.sin θ ≠ 0 := hsinθ_pos.ne'
      have hsin2_ne : Real.sin θ ^ 2 ≠ 0 := pow_ne_zero _ hsin_ne
      have hsq : a ^ 2 + b ^ 2 = (v 0 ^ 2 + v 1 ^ 2) / Real.sin θ ^ 2 := by
        rw [ha_def, hb_def]
        field_simp
      rw [hsq, ← hsinθ_sq]
      field_simp
    have ha_le : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
    have ha_lb : -1 ≤ a := by nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
    have ha_ub : a ≤ 1 := by nlinarith [sq_nonneg (a + 1), sq_nonneg (a - 1)]
    set φ₀ : ℝ := Real.arccos a with hφ₀_def
    have hφ₀_nn : 0 ≤ φ₀ := Real.arccos_nonneg _
    have hφ₀_le : φ₀ ≤ Real.pi := Real.arccos_le_pi _
    have hcosφ₀ : Real.cos φ₀ = a := Real.cos_arccos ha_lb ha_ub
    have hsinφ₀ : Real.sin φ₀ = Real.sqrt (1 - a^2) := by
      rw [hφ₀_def, Real.sin_arccos]
    have hsinφ₀_eq_abs_b : Real.sin φ₀ = |b| := by
      rw [hsinφ₀]
      have h1ma2 : 1 - a^2 = b^2 := by linarith
      rw [h1ma2]
      exact Real.sqrt_sq_eq_abs b
    have ha_mul : a * Real.sin θ = v 0 := by
      rw [ha_def]; field_simp
    have hb_mul : b * Real.sin θ = v 1 := by
      rw [hb_def]; field_simp
    by_cases hb_sign : 0 ≤ b
    · refine ⟨![θ, φ₀], ?_, ?_⟩
      · rw [sphCap_rect_mem_iff]
        have h0 : (![θ, φ₀] : Fin 2 → ℝ) 0 = θ := rfl
        have h1 : (![θ, φ₀] : Fin 2 → ℝ) 1 = φ₀ := rfl
        rw [h0, h1]
        refine ⟨hθ_nn, hθ_le, hφ₀_nn, ?_⟩
        linarith [Real.pi_nonneg]
      · have hsinφ₀_eq_b : Real.sin φ₀ = b := by
          rw [hsinφ₀_eq_abs_b, abs_of_nonneg hb_sign]
        apply PiLp.ext
        intro i
        fin_cases i
        · change sphCap_polar ![θ, φ₀] 0 = v 0
          rw [sphCap_polar_apply_zero]
          change Real.sin (![θ, φ₀] 0 : ℝ) * Real.cos (![θ, φ₀] 1 : ℝ) = v 0
          have : (![θ, φ₀] : Fin 2 → ℝ) 0 = θ := rfl
          have h1 : (![θ, φ₀] : Fin 2 → ℝ) 1 = φ₀ := rfl
          rw [this, h1, hcosφ₀, mul_comm, ha_mul]
        · change sphCap_polar ![θ, φ₀] 1 = v 1
          rw [sphCap_polar_apply_one]
          change Real.sin (![θ, φ₀] 0 : ℝ) * Real.sin (![θ, φ₀] 1 : ℝ) = v 1
          have : (![θ, φ₀] : Fin 2 → ℝ) 0 = θ := rfl
          have h1 : (![θ, φ₀] : Fin 2 → ℝ) 1 = φ₀ := rfl
          rw [this, h1, hsinφ₀_eq_b, mul_comm, hb_mul]
        · change sphCap_polar ![θ, φ₀] 2 = v 2
          rw [sphCap_polar_apply_two]
          change Real.cos (![θ, φ₀] 0 : ℝ) = v 2
          have : (![θ, φ₀] : Fin 2 → ℝ) 0 = θ := rfl
          rw [this, hcosθ]
    · push Not at hb_sign
      refine ⟨![θ, 2 * Real.pi - φ₀], ?_, ?_⟩
      · rw [sphCap_rect_mem_iff]
        have h0 : (![θ, 2 * Real.pi - φ₀] : Fin 2 → ℝ) 0 = θ := rfl
        have h1 : (![θ, 2 * Real.pi - φ₀] : Fin 2 → ℝ) 1 = 2 * Real.pi - φ₀ := rfl
        rw [h0, h1]
        refine ⟨hθ_nn, hθ_le, ?_, ?_⟩
        · linarith [Real.pi_nonneg]
        · linarith
      · have hcos_2pi_sub : Real.cos (2 * Real.pi - φ₀) = Real.cos φ₀ := by
          rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
        have hsin_2pi_sub : Real.sin (2 * Real.pi - φ₀) = - Real.sin φ₀ := by
          rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi]; ring
        have hsinφ₀_eq_neg_b : Real.sin φ₀ = -b := by
          rw [hsinφ₀_eq_abs_b, abs_of_neg hb_sign]
        apply PiLp.ext
        intro i
        fin_cases i
        · change sphCap_polar ![θ, 2 * Real.pi - φ₀] 0 = v 0
          rw [sphCap_polar_apply_zero]
          change Real.sin (![θ, 2 * Real.pi - φ₀] 0 : ℝ) *
              Real.cos (![θ, 2 * Real.pi - φ₀] 1 : ℝ) = v 0
          have h0 : (![θ, 2 * Real.pi - φ₀] : Fin 2 → ℝ) 0 = θ := rfl
          have h1 : (![θ, 2 * Real.pi - φ₀] : Fin 2 → ℝ) 1 = 2 * Real.pi - φ₀ := rfl
          rw [h0, h1, hcos_2pi_sub, hcosφ₀, mul_comm, ha_mul]
        · change sphCap_polar ![θ, 2 * Real.pi - φ₀] 1 = v 1
          rw [sphCap_polar_apply_one]
          change Real.sin (![θ, 2 * Real.pi - φ₀] 0 : ℝ) *
              Real.sin (![θ, 2 * Real.pi - φ₀] 1 : ℝ) = v 1
          have h0 : (![θ, 2 * Real.pi - φ₀] : Fin 2 → ℝ) 0 = θ := rfl
          have h1 : (![θ, 2 * Real.pi - φ₀] : Fin 2 → ℝ) 1 = 2 * Real.pi - φ₀ := rfl
          rw [h0, h1, hsin_2pi_sub, hsinφ₀_eq_neg_b]
          have : Real.sin θ * -(-b) = b * Real.sin θ := by ring
          rw [this, hb_mul]
        · change sphCap_polar ![θ, 2 * Real.pi - φ₀] 2 = v 2
          rw [sphCap_polar_apply_two]
          change Real.cos (![θ, 2 * Real.pi - φ₀] 0 : ℝ) = v 2
          have h0 : (![θ, 2 * Real.pi - φ₀] : Fin 2 → ℝ) 0 = θ := rfl
          rw [h0, hcosθ]

/-- The unit sphere `S² ⊂ ℝ³` has 2-dimensional Hausdorff measure at most `8π²`. -/
private lemma sphCap_unit_sphere_measure_le :
    μH[(2 : ℝ)] {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} ≤
      ENNReal.ofReal (8 * Real.pi ^ 2) := by
  have h_sub : {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} ⊆ sphCap_polar '' sphCap_rect :=
    sphCap_polar_surj_unit_sphere
  have h_mono := MeasureTheory.measure_mono (μ := μH[(2 : ℝ)]) h_sub
  have h_lip := sphCap_polar_lipschitz.hausdorffMeasure_image_le
    (d := (2 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2) sphCap_rect
  have h_hd_pi_real : (μH[(2 : ℝ)] : MeasureTheory.Measure (Fin 2 → ℝ)) =
      MeasureTheory.volume := by
    have h_card : ((Fintype.card (Fin 2) : ℕ) : ℝ) = 2 := by simp
    calc (μH[(2 : ℝ)] : MeasureTheory.Measure (Fin 2 → ℝ))
        = (μH[((Fintype.card (Fin 2) : ℕ) : ℝ)] : MeasureTheory.Measure (Fin 2 → ℝ)) := by
          rw [h_card]
      _ = MeasureTheory.volume := MeasureTheory.hausdorffMeasure_pi_real
  have h_vol_R : MeasureTheory.volume sphCap_rect = ENNReal.ofReal (2 * Real.pi ^ 2) := by
    unfold sphCap_rect
    rw [Real.volume_Icc_pi]
    rw [Fin.prod_univ_two]
    change ENNReal.ofReal (![Real.pi, 2 * Real.pi] 0 - ![(0:ℝ), 0] 0) *
         ENNReal.ofReal (![Real.pi, 2 * Real.pi] 1 - ![(0:ℝ), 0] 1) =
         ENNReal.ofReal (2 * Real.pi ^ 2)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    rw [← ENNReal.ofReal_mul Real.pi_nonneg]
    congr 1
    ring
  have h_hd_R : μH[(2 : ℝ)] sphCap_rect = ENNReal.ofReal (2 * Real.pi ^ 2) := by
    have : (μH[(2 : ℝ)] : MeasureTheory.Measure (Fin 2 → ℝ)) sphCap_rect =
        MeasureTheory.volume sphCap_rect := by
      rw [h_hd_pi_real]
    rw [this, h_vol_R]
  have h_two_rpow : ((2 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) = 4 := by
    rw [show ((2 : ℝ≥0) : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast]
    rw [ENNReal.rpow_natCast]
    norm_num
  calc μH[(2 : ℝ)] {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}
      ≤ μH[(2 : ℝ)] (sphCap_polar '' sphCap_rect) := h_mono
    _ ≤ ((2 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) * μH[(2 : ℝ)] sphCap_rect := h_lip
    _ = 4 * ENNReal.ofReal (2 * Real.pi ^ 2) := by rw [h_hd_R, h_two_rpow]
    _ = ENNReal.ofReal 4 * ENNReal.ofReal (2 * Real.pi ^ 2) := by
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from by
            rw [ENNReal.ofReal_ofNat]]
    _ = ENNReal.ofReal (8 * Real.pi ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring

/-- Helper: bound the squared distance to the polar cap basepoint y₀.
For `v` with `‖v‖ = 1` and `dist v y₀ ≤ 2r`, we have `‖v - y₀‖² ≤ 4r²`. -/
private lemma sphCap_sqrt_diff_bound
    {s t : ℝ} (hs_le : s ≤ 8 / 9) (ht_le : t ≤ 8 / 9)
    (hδ : |s - t| ≤ δ) (hδ_nn : 0 ≤ δ) :
    |Real.sqrt (1 - s) - Real.sqrt (1 - t)| ≤ (3 / 2) * δ := by
  have h1ms_nn : 0 ≤ 1 - s := by linarith
  have h1mt_nn : 0 ≤ 1 - t := by linarith
  have h1ms_ge : 1 / 9 ≤ 1 - s := by linarith
  have h1mt_ge : 1 / 9 ≤ 1 - t := by linarith
  have hsqrt_s_ge : (1 : ℝ) / 3 ≤ Real.sqrt (1 - s) := by
    have := Real.sqrt_le_sqrt h1ms_ge
    have h13 : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
      rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [h13] at this; exact this
  have hsqrt_t_ge : (1 : ℝ) / 3 ≤ Real.sqrt (1 - t) := by
    have := Real.sqrt_le_sqrt h1mt_ge
    have h13 : Real.sqrt (1 / 9 : ℝ) = 1 / 3 := by
      rw [show (1 / 9 : ℝ) = (1 / 3) ^ 2 by ring]
      exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [h13] at this; exact this
  have hsqrt_s_nn : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hsqrt_t_nn : 0 ≤ Real.sqrt (1 - t) := Real.sqrt_nonneg _
  have hsum_ge : (2 : ℝ) / 3 ≤ Real.sqrt (1 - s) + Real.sqrt (1 - t) := by linarith
  have hsum_pos : (0 : ℝ) < Real.sqrt (1 - s) + Real.sqrt (1 - t) := by linarith
  have hidentity : (Real.sqrt (1 - s) - Real.sqrt (1 - t)) *
      (Real.sqrt (1 - s) + Real.sqrt (1 - t)) = (1 - s) - (1 - t) := by
    rw [mul_comm]
    have hsq_s : Real.sqrt (1 - s) * Real.sqrt (1 - s) = 1 - s :=
      Real.mul_self_sqrt h1ms_nn
    have hsq_t : Real.sqrt (1 - t) * Real.sqrt (1 - t) = 1 - t :=
      Real.mul_self_sqrt h1mt_nn
    nlinarith [hsq_s, hsq_t]
  have habs_id : |Real.sqrt (1 - s) - Real.sqrt (1 - t)| *
      (Real.sqrt (1 - s) + Real.sqrt (1 - t)) = |s - t| := by
    have : |(Real.sqrt (1 - s) - Real.sqrt (1 - t)) *
        (Real.sqrt (1 - s) + Real.sqrt (1 - t))| = |(1 - s) - (1 - t)| := by
      rw [hidentity]
    rw [abs_mul, abs_of_nonneg hsum_pos.le] at this
    rw [this]
    rw [show (1 - s) - (1 - t) = -(s - t) by ring, abs_neg]
  have hdiff_eq : |Real.sqrt (1 - s) - Real.sqrt (1 - t)| =
      |s - t| / (Real.sqrt (1 - s) + Real.sqrt (1 - t)) := by
    rw [eq_div_iff hsum_pos.ne']
    exact habs_id
  rw [hdiff_eq]
  have h_div_le : |s - t| / (Real.sqrt (1 - s) + Real.sqrt (1 - t)) ≤ δ / (2/3) := by
    apply div_le_div₀ (by linarith) hδ (by norm_num) hsum_ge
  have h_dr_eq : δ / (2/3) = (3/2) * δ := by ring
  rw [← h_dr_eq]; exact h_div_le

set_option maxHeartbeats 800000 in
-- The two-case split (r ≥ 1/3 vs r < 1/3) and the Parseval-style decomposition
-- of the tangent-plane parametrization make this proof expensive to elaborate.
/-- Geometric core, for `r > 0`: the spherical cap bound. This is where the
2-AD-regularity of the unit sphere enters. -/
lemma sphere_cap_bound_pos
    (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r) :
    ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
        {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1})
      (Metric.closedBall x r) ≤ ENNReal.ofReal (1000 * r ^ 2) := by
  by_cases hr_large : r ≥ 1/3
  · have h_subset :
        ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
            {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1})
          (Metric.closedBall x r) ≤
        μH[(2 : ℝ)] {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} := by
      have hmeas : MeasurableSet {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} := by
        have hcont : Continuous fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ := continuous_norm
        exact hcont.measurable (measurableSet_singleton 1)
      have h_restrict_apply :
          ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
              {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}) (Metric.closedBall x r) =
          (μH[(2 : ℝ)] : MeasureTheory.Measure _)
            (Metric.closedBall x r ∩ {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}) :=
        MeasureTheory.Measure.restrict_apply' hmeas
      rw [h_restrict_apply]
      exact MeasureTheory.measure_mono Set.inter_subset_right
    have h_sphere_le : μH[(2 : ℝ)] {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} ≤
        ENNReal.ofReal (8 * Real.pi ^ 2) := sphCap_unit_sphere_measure_le
    have h_pi_lt : Real.pi < 3.15 := Real.pi_lt_d2
    have h_pi_nn : 0 ≤ Real.pi := Real.pi_nonneg
    have h_8pi2_le : 8 * Real.pi ^ 2 ≤ 1000 * r ^ 2 := by
      have hpi2 : Real.pi ^ 2 ≤ 9.9225 := by nlinarith
      have h_8pi2 : 8 * Real.pi ^ 2 ≤ 79.38 := by linarith
      have hr2 : 1 / 9 ≤ r ^ 2 := by
        have : (1/3 : ℝ) ^ 2 ≤ r ^ 2 := by
          have h13_nn : (0 : ℝ) ≤ 1/3 := by norm_num
          exact pow_le_pow_left₀ h13_nn hr_large 2
        nlinarith
      nlinarith
    calc ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
            {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1})
          (Metric.closedBall x r)
        ≤ μH[(2 : ℝ)] {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} := h_subset
      _ ≤ ENNReal.ofReal (8 * Real.pi ^ 2) := h_sphere_le
      _ ≤ ENNReal.ofReal (1000 * r ^ 2) :=
          ENNReal.ofReal_le_ofReal h_8pi2_le
  · push Not at hr_large
    set cap : Set (EuclideanSpace ℝ (Fin 3)) :=
      Metric.closedBall x r ∩ {v | ‖v‖ = 1} with hcap_def
    by_cases hcap_empty : cap = ∅
    · have hmeas : MeasurableSet {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} := by
        have hcont : Continuous fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ := continuous_norm
        exact hcont.measurable (measurableSet_singleton 1)
      rw [MeasureTheory.Measure.restrict_apply' hmeas]
      rw [← hcap_def]
      rw [hcap_empty]
      simp
    · obtain ⟨y₀, hy₀_cap⟩ := Set.nonempty_iff_ne_empty.mpr hcap_empty
      have hy₀_dist : dist y₀ x ≤ r := hy₀_cap.1
      have hy₀_norm : ‖y₀‖ = 1 := hy₀_cap.2
      have hy_ne : (y₀ : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
        intro h
        have : ‖y₀‖ = 0 := by rw [h]; exact norm_zero
        rw [hy₀_norm] at this
        linarith
      haveI hfact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
      let b : OrthonormalBasis (Fin 2) ℝ ((ℝ ∙ y₀)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :=
        OrthonormalBasis.fromOrthogonalSpanSingleton 2 hy_ne
      let e₀ : EuclideanSpace ℝ (Fin 3) := ((b 0 : (ℝ ∙ y₀)ᗮ) : EuclideanSpace ℝ (Fin 3))
      let e₁ : EuclideanSpace ℝ (Fin 3) := ((b 1 : (ℝ ∙ y₀)ᗮ) : EuclideanSpace ℝ (Fin 3))
      have he₀_mem : (b 0 : (ℝ ∙ y₀)ᗮ).val ∈ ((ℝ ∙ y₀)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :=
        (b 0).2
      have he₁_mem : (b 1 : (ℝ ∙ y₀)ᗮ).val ∈ ((ℝ ∙ y₀)ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) :=
        (b 1).2
      have hborth := b.orthonormal
      have he₀_norm_sq : inner ℝ e₀ e₀ = (1 : ℝ) := by
        have h := hborth.1 0
        have h2 : ‖(b 0 : (ℝ ∙ y₀)ᗮ)‖ = 1 := h
        have hh : inner ℝ ((b 0 : (ℝ ∙ y₀)ᗮ)) ((b 0 : (ℝ ∙ y₀)ᗮ)) = (1 : ℝ) := by
          rw [real_inner_self_eq_norm_sq, h2]; ring
        exact hh
      have he₁_norm_sq : inner ℝ e₁ e₁ = (1 : ℝ) := by
        have h := hborth.1 1
        have h2 : ‖(b 1 : (ℝ ∙ y₀)ᗮ)‖ = 1 := h
        have hh : inner ℝ ((b 1 : (ℝ ∙ y₀)ᗮ)) ((b 1 : (ℝ ∙ y₀)ᗮ)) = (1 : ℝ) := by
          rw [real_inner_self_eq_norm_sq, h2]; ring
        exact hh
      have he₀_e₁ : inner ℝ e₀ e₁ = (0 : ℝ) := by
        have h := hborth.2 (show (0 : Fin 2) ≠ 1 by decide)
        exact h
      have he₁_e₀ : inner ℝ e₁ e₀ = (0 : ℝ) := by
        rw [real_inner_comm]; exact he₀_e₁
      have hy₀_mem : (y₀ : EuclideanSpace ℝ (Fin 3)) ∈ (ℝ ∙ y₀) :=
        Submodule.mem_span_singleton_self _
      have he₀_y₀ : inner ℝ e₀ (y₀ : EuclideanSpace ℝ (Fin 3)) = (0 : ℝ) :=
        Submodule.inner_left_of_mem_orthogonal hy₀_mem he₀_mem
      have he₁_y₀ : inner ℝ e₁ (y₀ : EuclideanSpace ℝ (Fin 3)) = (0 : ℝ) :=
        Submodule.inner_left_of_mem_orthogonal hy₀_mem he₁_mem
      have hy₀_e₀ : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) e₀ = (0 : ℝ) := by
        rw [real_inner_comm]; exact he₀_y₀
      have hy₀_e₁ : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) e₁ = (0 : ℝ) := by
        rw [real_inner_comm]; exact he₁_y₀
      have hy₀_y₀ : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) y₀ = (1 : ℝ) := by
        rw [real_inner_self_eq_norm_sq, hy₀_norm]; ring
      have he₀_norm : ‖e₀‖ = 1 := hborth.1 0
      have he₁_norm : ‖e₁‖ = 1 := hborth.1 1
      let f : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 3) := fun u =>
        (u 0) • e₀ + (u 1) • e₁ +
          Real.sqrt (max 0 (1 - u 0 ^ 2 - u 1 ^ 2)) • (y₀ : EuclideanSpace ℝ (Fin 3))
      have hf_diff_sq : ∀ u v : Fin 2 → ℝ,
          ‖f u - f v‖ ^ 2 =
            (u 0 - v 0) ^ 2 + (u 1 - v 1) ^ 2 +
              (Real.sqrt (max 0 (1 - u 0 ^ 2 - u 1 ^ 2)) -
                Real.sqrt (max 0 (1 - v 0 ^ 2 - v 1 ^ 2))) ^ 2 := by
        intro u v
        set su := Real.sqrt (max 0 (1 - u 0 ^ 2 - u 1 ^ 2))
        set sv := Real.sqrt (max 0 (1 - v 0 ^ 2 - v 1 ^ 2))
        have hdiff : f u - f v =
            (u 0 - v 0) • e₀ + (u 1 - v 1) • e₁ + (su - sv) • (y₀ : EuclideanSpace ℝ (Fin 3)) := by
          change ((u 0) • e₀ + (u 1) • e₁ + su • (y₀ : EuclideanSpace ℝ (Fin 3))) -
                  ((v 0) • e₀ + (v 1) • e₁ + sv • (y₀ : EuclideanSpace ℝ (Fin 3))) =
              (u 0 - v 0) • e₀ + (u 1 - v 1) • e₁ + (su - sv) • (y₀ : EuclideanSpace ℝ (Fin 3))
          module
        rw [hdiff]
        rw [← real_inner_self_eq_norm_sq]
        set a := u 0 - v 0
        set b := u 1 - v 1
        set c := su - sv
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          he₀_norm_sq, he₁_norm_sq, hy₀_y₀, he₀_e₁, he₀_y₀, he₁_y₀,
          he₁_e₀, hy₀_e₀, hy₀_e₁]
        ring
      set D : Set (Fin 2 → ℝ) := Metric.closedBall (0 : Fin 2 → ℝ) (2 * r) with hD_def
      have hD_mem_iff : ∀ u : Fin 2 → ℝ, u ∈ D ↔ |u 0| ≤ 2 * r ∧ |u 1| ≤ 2 * r := by
        intro u
        constructor
        · intro hu
          rw [hD_def, Metric.mem_closedBall, dist_pi_le_iff (by linarith)] at hu
          have h0 := hu 0
          have h1 := hu 1
          rw [show (0 : Fin 2 → ℝ) 0 = 0 from rfl, Real.dist_eq, sub_zero] at h0
          rw [show (0 : Fin 2 → ℝ) 1 = 0 from rfl, Real.dist_eq, sub_zero] at h1
          exact ⟨h0, h1⟩
        · intro ⟨h0, h1⟩
          rw [hD_def, Metric.mem_closedBall]
          rw [dist_pi_le_iff (by linarith)]
          intro i
          fin_cases i
          · change dist (u 0) ((0 : Fin 2 → ℝ) 0) ≤ 2 * r
            rw [show (0 : Fin 2 → ℝ) 0 = 0 from rfl, Real.dist_eq, sub_zero]; exact h0
          · change dist (u 1) ((0 : Fin 2 → ℝ) 1) ≤ 2 * r
            rw [show (0 : Fin 2 → ℝ) 1 = 0 from rfl, Real.dist_eq, sub_zero]; exact h1
      have hu_sq_bound : ∀ u ∈ D, u 0 ^ 2 + u 1 ^ 2 ≤ 8 / 9 := by
        intro u hu
        rcases (hD_mem_iff u).mp hu with ⟨h0, h1⟩
        have hu0_sq : u 0 ^ 2 ≤ (2 * r) ^ 2 := by
          have h0_abs2 : |u 0| ^ 2 = u 0 ^ 2 := sq_abs _
          nlinarith [abs_nonneg (u 0), h0]
        have hu1_sq : u 1 ^ 2 ≤ (2 * r) ^ 2 := by
          have h1_abs2 : |u 1| ^ 2 = u 1 ^ 2 := sq_abs _
          nlinarith [abs_nonneg (u 1), h1]
        have h_2r_sq : (2 * r) ^ 2 ≤ 4 / 9 := by
          have hr_nn : 0 ≤ r := hr.le
          nlinarith [hr_large]
        nlinarith
      have h_sqrt_eq : ∀ u ∈ D,
          Real.sqrt (max 0 (1 - u 0 ^ 2 - u 1 ^ 2)) = Real.sqrt (1 - u 0 ^ 2 - u 1 ^ 2) := by
        intro u hu
        have hsq := hu_sq_bound u hu
        have : 1 - u 0 ^ 2 - u 1 ^ 2 ≥ 1 / 9 := by linarith
        have h_nn : 0 ≤ 1 - u 0 ^ 2 - u 1 ^ 2 := by linarith
        rw [max_eq_right h_nn]
      have hf_lip : LipschitzOnWith 5 f D := by
        rw [lipschitzOnWith_iff_dist_le_mul]
        intro u hu v hv
        have hsu_eq := h_sqrt_eq u hu
        have hsv_eq := h_sqrt_eq v hv
        have hu_sq := hu_sq_bound u hu
        have hv_sq := hu_sq_bound v hv
        have hu0_abs : |u 0| ≤ 2 * r := ((hD_mem_iff u).mp hu).1
        have hu1_abs : |u 1| ≤ 2 * r := ((hD_mem_iff u).mp hu).2
        have hv0_abs : |v 0| ≤ 2 * r := ((hD_mem_iff v).mp hv).1
        have hv1_abs : |v 1| ≤ 2 * r := ((hD_mem_iff v).mp hv).2
        have hduv_0 : |u 0 - v 0| ≤ dist u v := by
          have := dist_le_pi_dist u v 0; rwa [Real.dist_eq] at this
        have hduv_1 : |u 1 - v 1| ≤ dist u v := by
          have := dist_le_pi_dist u v 1; rwa [Real.dist_eq] at this
        have hsq0_diff : |u 0 ^ 2 - v 0 ^ 2| ≤ 4 * r * dist u v := by
          have h_eq : u 0 ^ 2 - v 0 ^ 2 = (u 0 + v 0) * (u 0 - v 0) := by ring
          rw [h_eq, abs_mul]
          have h_sum : |u 0 + v 0| ≤ 4 * r := by
            calc |u 0 + v 0| ≤ |u 0| + |v 0| := abs_add_le _ _
              _ ≤ 2 * r + 2 * r := by linarith
              _ = 4 * r := by ring
          have hsum_nn : 0 ≤ |u 0 + v 0| := abs_nonneg _
          have hdiff_nn : 0 ≤ |u 0 - v 0| := abs_nonneg _
          calc |u 0 + v 0| * |u 0 - v 0| ≤ (4 * r) * |u 0 - v 0| :=
                mul_le_mul_of_nonneg_right h_sum hdiff_nn
            _ ≤ (4 * r) * dist u v := by
                have h4r_nn : 0 ≤ 4 * r := by linarith
                exact mul_le_mul_of_nonneg_left hduv_0 h4r_nn
            _ = 4 * r * dist u v := rfl
        have hsq1_diff : |u 1 ^ 2 - v 1 ^ 2| ≤ 4 * r * dist u v := by
          have h_eq : u 1 ^ 2 - v 1 ^ 2 = (u 1 + v 1) * (u 1 - v 1) := by ring
          rw [h_eq, abs_mul]
          have h_sum : |u 1 + v 1| ≤ 4 * r := by
            calc |u 1 + v 1| ≤ |u 1| + |v 1| := abs_add_le _ _
              _ ≤ 2 * r + 2 * r := by linarith
              _ = 4 * r := by ring
          have hsum_nn : 0 ≤ |u 1 + v 1| := abs_nonneg _
          have hdiff_nn : 0 ≤ |u 1 - v 1| := abs_nonneg _
          calc |u 1 + v 1| * |u 1 - v 1| ≤ (4 * r) * |u 1 - v 1| :=
                mul_le_mul_of_nonneg_right h_sum hdiff_nn
            _ ≤ (4 * r) * dist u v := by
                have h4r_nn : 0 ≤ 4 * r := by linarith
                exact mul_le_mul_of_nonneg_left hduv_1 h4r_nn
            _ = 4 * r * dist u v := rfl
        have h_st_diff : |(u 0 ^ 2 + u 1 ^ 2) - (v 0 ^ 2 + v 1 ^ 2)| ≤ 8 * r * dist u v := by
          have h_eq : (u 0 ^ 2 + u 1 ^ 2) - (v 0 ^ 2 + v 1 ^ 2) =
              (u 0 ^ 2 - v 0 ^ 2) + (u 1 ^ 2 - v 1 ^ 2) := by ring
          rw [h_eq]
          calc |(u 0 ^ 2 - v 0 ^ 2) + (u 1 ^ 2 - v 1 ^ 2)|
              ≤ |u 0 ^ 2 - v 0 ^ 2| + |u 1 ^ 2 - v 1 ^ 2| := abs_add_le _ _
            _ ≤ 4 * r * dist u v + 4 * r * dist u v := by linarith
            _ = 8 * r * dist u v := by ring
        have hduv_nn : 0 ≤ dist u v := dist_nonneg
        have h8r_d_nn : 0 ≤ 8 * r * dist u v := by positivity
        have h_sqrt_diff : |Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) -
              Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2))| ≤ (3 / 2) * (8 * r * dist u v) := by
          apply sphCap_sqrt_diff_bound (by linarith) (by linarith)
            h_st_diff h8r_d_nn
        have hr_le_third : 8 * r * dist u v ≤ (8 / 3) * dist u v := by
          have hrr : r ≤ 1 / 3 := hr_large.le
          have hduv_nn := dist_nonneg (x := u) (y := v)
          nlinarith
        have h_sqrt_diff_4 : |Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) -
              Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2))| ≤ 4 * dist u v := by
          calc |Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) -
                  Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2))|
              ≤ (3 / 2) * (8 * r * dist u v) := h_sqrt_diff
            _ ≤ (3 / 2) * ((8 / 3) * dist u v) := by
                apply mul_le_mul_of_nonneg_left hr_le_third (by norm_num)
            _ = 4 * dist u v := by ring
        have h_norm_sq_le : ‖f u - f v‖ ^ 2 ≤ (5 * dist u v) ^ 2 := by
          rw [hf_diff_sq]
          have h0_diff : (u 0 - v 0) ^ 2 ≤ (dist u v) ^ 2 := by
            have h := hduv_0
            have habs2 : (u 0 - v 0) ^ 2 = |u 0 - v 0| ^ 2 := (sq_abs _).symm
            rw [habs2]
            apply sq_le_sq' (by linarith [abs_nonneg (u 0 - v 0)]) h
          have h1_diff : (u 1 - v 1) ^ 2 ≤ (dist u v) ^ 2 := by
            have h := hduv_1
            have habs2 : (u 1 - v 1) ^ 2 = |u 1 - v 1| ^ 2 := (sq_abs _).symm
            rw [habs2]
            apply sq_le_sq' (by linarith [abs_nonneg (u 1 - v 1)]) h
          have h_su_form :
              Real.sqrt (max 0 (1 - u 0 ^ 2 - u 1 ^ 2)) =
                Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) := by
            rw [hsu_eq]; congr 1; ring
          have h_sv_form :
              Real.sqrt (max 0 (1 - v 0 ^ 2 - v 1 ^ 2)) =
                Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2)) := by
            rw [hsv_eq]; congr 1; ring
          rw [h_su_form, h_sv_form]
          have h_third : (Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) -
              Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2))) ^ 2 ≤ (4 * dist u v) ^ 2 := by
            have habs2 : (Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) -
                Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2))) ^ 2 =
                |Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) -
                Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2))| ^ 2 := (sq_abs _).symm
            rw [habs2]
            have h_4d_nn : 0 ≤ 4 * dist u v := by positivity
            have h_abs_nn := abs_nonneg (Real.sqrt (1 - (u 0 ^ 2 + u 1 ^ 2)) -
                Real.sqrt (1 - (v 0 ^ 2 + v 1 ^ 2)))
            apply sq_le_sq' (by linarith) h_sqrt_diff_4
          have h_5dist_sq : (5 * dist u v) ^ 2 = 25 * dist u v ^ 2 := by ring
          have h_4dist_sq : (4 * dist u v) ^ 2 = 16 * dist u v ^ 2 := by ring
          rw [h_5dist_sq]; rw [h_4dist_sq] at h_third
          have hd2_nn : 0 ≤ dist u v ^ 2 := sq_nonneg _
          linarith [h0_diff, h1_diff, h_third, hd2_nn]
        have h_5dist_nn : 0 ≤ 5 * dist u v := by positivity
        have h_norm_le : ‖f u - f v‖ ≤ 5 * dist u v := by
          have h_norm_nn : 0 ≤ ‖f u - f v‖ := norm_nonneg _
          have := Real.sqrt_le_sqrt h_norm_sq_le
          rw [Real.sqrt_sq h_norm_nn, Real.sqrt_sq h_5dist_nn] at this
          exact this
        have hcoe : ((5 : ℝ≥0) : ℝ) = 5 := by norm_num
        rw [dist_eq_norm]
        rw [hcoe]
        exact h_norm_le
      let bFull_fn : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
        ![e₀, e₁, (y₀ : EuclideanSpace ℝ (Fin 3))]
      have hbFull_orth : Orthonormal ℝ bFull_fn := by
        refine ⟨?_, ?_⟩
        · intro i
          fin_cases i
          · change ‖e₀‖ = 1; exact he₀_norm
          · change ‖e₁‖ = 1; exact he₁_norm
          · change ‖(y₀ : EuclideanSpace ℝ (Fin 3))‖ = 1; exact hy₀_norm
        · intro i j hij
          fin_cases i <;> fin_cases j
          · exact absurd rfl hij
          · change inner ℝ e₀ e₁ = (0 : ℝ); exact he₀_e₁
          · change inner ℝ e₀ (y₀ : EuclideanSpace ℝ (Fin 3)) = (0 : ℝ); exact he₀_y₀
          · change inner ℝ e₁ e₀ = (0 : ℝ); exact he₁_e₀
          · exact absurd rfl hij
          · change inner ℝ e₁ (y₀ : EuclideanSpace ℝ (Fin 3)) = (0 : ℝ); exact he₁_y₀
          · change inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) e₀ = (0 : ℝ); exact hy₀_e₀
          · change inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) e₁ = (0 : ℝ); exact hy₀_e₁
          · exact absurd rfl hij
      have hcard_eq : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
        simp
      let bFull_basis : Module.Basis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
        basisOfOrthonormalOfCardEqFinrank hbFull_orth hcard_eq
      have hbFull_basis_apply : ∀ i, bFull_basis i = bFull_fn i :=
        fun i => congrFun (coe_basisOfOrthonormalOfCardEqFinrank hbFull_orth hcard_eq) i
      let bFull : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
        bFull_basis.toOrthonormalBasis (by
          have : Orthonormal ℝ (bFull_basis : Fin 3 → EuclideanSpace ℝ (Fin 3)) := by
            have h_eq : (bFull_basis : Fin 3 → EuclideanSpace ℝ (Fin 3)) = bFull_fn := by
              funext i; exact hbFull_basis_apply i
            rw [h_eq]; exact hbFull_orth
          exact this)
      have hbFull_apply : ∀ i, bFull i = bFull_fn i := by
        intro i
        have h_coe : (bFull : Fin 3 → EuclideanSpace ℝ (Fin 3)) = bFull_basis :=
          bFull_basis.coe_toOrthonormalBasis _
        have : (bFull : Fin 3 → EuclideanSpace ℝ (Fin 3)) i = bFull_basis i := by
          rw [h_coe]
        rw [this, hbFull_basis_apply]
      have hbFull_0 : (bFull 0 : EuclideanSpace ℝ (Fin 3)) = e₀ := hbFull_apply 0
      have hbFull_1 : (bFull 1 : EuclideanSpace ℝ (Fin 3)) = e₁ := hbFull_apply 1
      have hbFull_2 : (bFull 2 : EuclideanSpace ℝ (Fin 3)) = y₀ := hbFull_apply 2
      have h_decomp : ∀ v : EuclideanSpace ℝ (Fin 3),
          v = inner ℝ e₀ v • e₀ + inner ℝ e₁ v • e₁ +
              inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v • y₀ := by
        intro v
        have h_sum_repr := bFull.sum_repr v
        rw [Fin.sum_univ_three] at h_sum_repr
        have h_repr_0 : bFull.repr v 0 = inner ℝ e₀ v := by
          rw [bFull.repr_apply_apply v 0, hbFull_0]
        have h_repr_1 : bFull.repr v 1 = inner ℝ e₁ v := by
          rw [bFull.repr_apply_apply v 1, hbFull_1]
        have h_repr_2 : bFull.repr v 2 = inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := by
          rw [bFull.repr_apply_apply v 2, hbFull_2]
        rw [h_repr_0, h_repr_1, h_repr_2, hbFull_0, hbFull_1, hbFull_2] at h_sum_repr
        exact h_sum_repr.symm
      have h_parseval : ∀ v : EuclideanSpace ℝ (Fin 3),
          ‖v‖ ^ 2 = inner ℝ e₀ v ^ 2 + inner ℝ e₁ v ^ 2 +
              inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 := by
        intro v
        have h_dec := h_decomp v
        have h_expand : ‖v‖ ^ 2 = inner ℝ v v := by
          rw [← real_inner_self_eq_norm_sq]
        rw [h_expand]
        conv_lhs => rw [h_dec]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          he₀_norm_sq, he₁_norm_sq, hy₀_y₀, he₀_e₁, he₀_y₀, he₁_y₀,
          he₁_e₀, hy₀_e₀, hy₀_e₁]
        ring
      have h_cap_sub : cap ⊆ f '' D := by
        intro v hv
        rcases hv with ⟨hv_dist, hv_norm⟩
        simp only [Set.mem_setOf_eq] at hv_norm
        let u_v : Fin 2 → ℝ := ![inner ℝ e₀ v, inner ℝ e₁ v]
        refine ⟨u_v, ?_, ?_⟩
        · rw [hD_def, Metric.mem_closedBall, dist_pi_le_iff (by linarith)]
          have hv_y₀_dist : dist v y₀ ≤ 2 * r := by
            calc dist v y₀ ≤ dist v x + dist x y₀ := dist_triangle _ _ _
              _ ≤ r + r := by
                  have h1 : dist v x ≤ r := hv_dist
                  have h2 : dist x y₀ ≤ r := by
                    rw [dist_comm]; exact hy₀_dist
                  linarith
              _ = 2 * r := by ring
          have hv_y₀_norm : ‖v - y₀‖ ≤ 2 * r := by
            rw [← dist_eq_norm]; exact hv_y₀_dist
          have hv_y₀_norm_sq : ‖v - y₀‖ ^ 2 ≤ (2 * r) ^ 2 := by
            have : 0 ≤ ‖v - y₀‖ := norm_nonneg _
            have h2r_nn : 0 ≤ 2 * r := by linarith
            nlinarith
          have h_norm_sub_eq : ‖v - y₀‖ ^ 2 = 2 -
              2 * inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := by
            rw [norm_sub_sq_real, hv_norm, hy₀_norm]
            have h_comm : inner ℝ v (y₀ : EuclideanSpace ℝ (Fin 3)) =
                inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := real_inner_comm _ _
            rw [h_comm]
            ring
          have h_inner_y₀_v_ge : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ≥ 1 - 2 * r ^ 2 := by
            have : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v = (2 - ‖v - y₀‖ ^ 2) / 2 := by
              linarith
            rw [this]
            have h_2r_sq_eq : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
            have : (2 - ‖v - y₀‖^2) / 2 ≥ (2 - 4 * r^2) / 2 := by
              have h1 : ‖v - y₀‖^2 ≤ 4 * r ^ 2 := by
                have := hv_y₀_norm_sq
                linarith [h_2r_sq_eq]
              linarith
            linarith
          have h_inner_y₀_v_nn : 0 ≤ inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := by
            have : 1 - 2 * r ^ 2 ≥ 0 := by
              have hrr : r ≤ 1/3 := hr_large.le
              nlinarith
            linarith
          have h_pars := h_parseval v
          rw [hv_norm] at h_pars
          have h_sum_e_sq : inner ℝ e₀ v ^ 2 + inner ℝ e₁ v ^ 2 =
              1 - inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 := by linarith
          have h_sum_e_sq_le : inner ℝ e₀ v ^ 2 + inner ℝ e₁ v ^ 2 ≤ 4 * r ^ 2 := by
            have h_lb := h_inner_y₀_v_ge
            have h_sq_lb : (1 - 2 * r ^ 2) ^ 2 ≤
                inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 := by
              have hr_nn : 0 ≤ r := hr.le
              have hrr : r ≤ 1/3 := hr_large.le
              have h_2r_le : 1 - 2 * r ^ 2 ≥ 0 := by nlinarith
              have habs : |1 - 2 * r ^ 2| ≤ |inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v| := by
                rw [abs_of_nonneg h_2r_le, abs_of_nonneg h_inner_y₀_v_nn]; exact h_lb
              have : (1 - 2 * r ^ 2) ^ 2 = |1 - 2 * r ^ 2| ^ 2 := (sq_abs _).symm
              rw [this]
              have h_v_abs : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 =
                  |inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v| ^ 2 := (sq_abs _).symm
              rw [h_v_abs]
              exact sq_le_sq' (by linarith [abs_nonneg (1 - 2 * r ^ 2)]) habs
            have hr_nn : 0 ≤ r := hr.le
            have hrr : r ≤ 1/3 := hr_large.le
            nlinarith [h_sum_e_sq, h_sq_lb]
          have h_e₀_sq_le : inner ℝ e₀ v ^ 2 ≤ 4 * r ^ 2 := by
            have := sq_nonneg (inner ℝ e₁ v); linarith
          have h_e₁_sq_le : inner ℝ e₁ v ^ 2 ≤ 4 * r ^ 2 := by
            have := sq_nonneg (inner ℝ e₀ v); linarith
          have h_e₀_abs : |inner ℝ e₀ v| ≤ 2 * r := by
            have h_eq : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
            have h_abs2 : inner ℝ e₀ v ^ 2 = |inner ℝ e₀ v| ^ 2 := (sq_abs _).symm
            have hr_nn : 0 ≤ 2 * r := by linarith
            have hpow_le : |inner ℝ e₀ v| ^ 2 ≤ (2 * r) ^ 2 := by
              rw [h_eq, ← h_abs2]; exact h_e₀_sq_le
            exact abs_le_of_sq_le_sq' hpow_le hr_nn |>.2
          have h_e₁_abs : |inner ℝ e₁ v| ≤ 2 * r := by
            have h_eq : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
            have h_abs2 : inner ℝ e₁ v ^ 2 = |inner ℝ e₁ v| ^ 2 := (sq_abs _).symm
            have hr_nn : 0 ≤ 2 * r := by linarith
            have hpow_le : |inner ℝ e₁ v| ^ 2 ≤ (2 * r) ^ 2 := by
              rw [h_eq, ← h_abs2]; exact h_e₁_sq_le
            exact abs_le_of_sq_le_sq' hpow_le hr_nn |>.2
          intro i
          fin_cases i
          · change dist (u_v 0) ((0 : Fin 2 → ℝ) 0) ≤ 2 * r
            change dist (inner ℝ e₀ v) (0 : ℝ) ≤ 2 * r
            rw [Real.dist_eq, sub_zero]; exact h_e₀_abs
          · change dist (u_v 1) ((0 : Fin 2 → ℝ) 1) ≤ 2 * r
            change dist (inner ℝ e₁ v) (0 : ℝ) ≤ 2 * r
            rw [Real.dist_eq, sub_zero]; exact h_e₁_abs
        · have h_e₀_sq_le_aux : inner ℝ e₀ v ^ 2 ≤ 1 := by
            have h_pars := h_parseval v
            rw [hv_norm] at h_pars
            have h1 : inner ℝ e₀ v ^ 2 ≤ inner ℝ e₀ v ^ 2 + inner ℝ e₁ v ^ 2 +
                inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 := by
              have := sq_nonneg (inner ℝ e₁ v)
              have := sq_nonneg (inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v)
              linarith
            linarith
          have h_e₁_sq_le_aux : inner ℝ e₁ v ^ 2 ≤ 1 := by
            have h_pars := h_parseval v
            rw [hv_norm] at h_pars
            have h1 : inner ℝ e₁ v ^ 2 ≤ inner ℝ e₀ v ^ 2 + inner ℝ e₁ v ^ 2 +
                inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 := by
              have := sq_nonneg (inner ℝ e₀ v)
              have := sq_nonneg (inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v)
              linarith
            linarith
          have hv_y₀_dist : dist v y₀ ≤ 2 * r := by
            have h1 : dist v x ≤ r := hv_dist
            have h2 : dist x y₀ ≤ r := by rw [dist_comm]; exact hy₀_dist
            calc dist v y₀ ≤ dist v x + dist x y₀ := dist_triangle _ _ _
              _ ≤ r + r := by linarith
              _ = 2 * r := by ring
          have hv_y₀_norm : ‖v - y₀‖ ≤ 2 * r := by rw [← dist_eq_norm]; exact hv_y₀_dist
          have hv_y₀_norm_sq : ‖v - y₀‖ ^ 2 ≤ (2 * r) ^ 2 := by
            have : 0 ≤ ‖v - y₀‖ := norm_nonneg _
            have h2r_nn : 0 ≤ 2 * r := by linarith
            nlinarith
          have h_norm_sub_eq : ‖v - y₀‖ ^ 2 = 2 -
              2 * inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := by
            rw [norm_sub_sq_real, hv_norm, hy₀_norm]
            have h_comm : inner ℝ v (y₀ : EuclideanSpace ℝ (Fin 3)) =
                inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := real_inner_comm _ _
            rw [h_comm]
            ring
          have h_inner_y₀_v_ge : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ≥ 1 - 2 * r ^ 2 := by
            have : inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v = (2 - ‖v - y₀‖ ^ 2) / 2 := by linarith
            rw [this]
            have h_2r_sq_eq : (2 * r) ^ 2 = 4 * r ^ 2 := by ring
            have : (2 - ‖v - y₀‖^2) / 2 ≥ (2 - 4 * r^2) / 2 := by
              have h1 : ‖v - y₀‖^2 ≤ 4 * r ^ 2 := by linarith [h_2r_sq_eq]
              linarith
            linarith
          have h_inner_y₀_v_nn : 0 ≤ inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := by
            have : 1 - 2 * r ^ 2 ≥ 0 := by
              have hrr : r ≤ 1/3 := hr_large.le
              nlinarith
            linarith
          have h_pars := h_parseval v
          rw [hv_norm] at h_pars
          have h_1_sub : 1 - u_v 0 ^ 2 - u_v 1 ^ 2 =
              inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 := by
            change 1 - inner ℝ e₀ v ^ 2 - inner ℝ e₁ v ^ 2 =
                inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2
            linarith
          have h_max_eq : max 0 (1 - u_v 0 ^ 2 - u_v 1 ^ 2) =
              inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v ^ 2 := by
            rw [h_1_sub, max_eq_right (sq_nonneg _)]
          have h_sqrt_eq_inner :
              Real.sqrt (max 0 (1 - u_v 0 ^ 2 - u_v 1 ^ 2)) =
                inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v := by
            rw [h_max_eq]
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h_inner_y₀_v_nn]
          change u_v 0 • e₀ + u_v 1 • e₁ +
              Real.sqrt (max 0 (1 - u_v 0 ^ 2 - u_v 1 ^ 2)) • (y₀ : EuclideanSpace ℝ (Fin 3)) = v
          rw [h_sqrt_eq_inner]
          change inner ℝ e₀ v • e₀ + inner ℝ e₁ v • e₁ +
              inner ℝ (y₀ : EuclideanSpace ℝ (Fin 3)) v • (y₀ : EuclideanSpace ℝ (Fin 3)) = v
          exact (h_decomp v).symm
      have h2_nn : (0 : ℝ) ≤ 2 := by norm_num
      have h_lip_img : μH[(2 : ℝ)] (f '' D) ≤
          ((5 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) * μH[(2 : ℝ)] D :=
        hf_lip.hausdorffMeasure_image_le h2_nn
      have h_hd_pi_real : (μH[(2 : ℝ)] : MeasureTheory.Measure (Fin 2 → ℝ)) =
          MeasureTheory.volume := by
        have h_card : ((Fintype.card (Fin 2) : ℕ) : ℝ) = 2 := by simp
        calc (μH[(2 : ℝ)] : MeasureTheory.Measure (Fin 2 → ℝ))
            = (μH[((Fintype.card (Fin 2) : ℕ) : ℝ)] :
                MeasureTheory.Measure (Fin 2 → ℝ)) := by rw [h_card]
          _ = MeasureTheory.volume := MeasureTheory.hausdorffMeasure_pi_real
      have h_2r_nn : (0 : ℝ) ≤ 2 * r := by linarith
      have h_vol_D : MeasureTheory.volume D = ENNReal.ofReal (16 * r ^ 2) := by
        rw [hD_def, Real.volume_pi_closedBall (0 : Fin 2 → ℝ) h_2r_nn]
        congr 1
        rw [Fintype.card_fin]
        ring
      have h_hd_D : μH[(2 : ℝ)] D = ENNReal.ofReal (16 * r ^ 2) := by
        have : (μH[(2 : ℝ)] : MeasureTheory.Measure (Fin 2 → ℝ)) D =
            MeasureTheory.volume D := by rw [h_hd_pi_real]
        rw [this, h_vol_D]
      have h_five_rpow : ((5 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) = 25 := by
        rw [show ((5 : ℝ≥0) : ℝ≥0∞) = ((5 : ℕ) : ℝ≥0∞) from by norm_cast]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast]
        rw [ENNReal.rpow_natCast]
        norm_num
      have h_img_le : μH[(2 : ℝ)] (f '' D) ≤ ENNReal.ofReal (400 * r ^ 2) := by
        calc μH[(2 : ℝ)] (f '' D)
            ≤ ((5 : ℝ≥0) : ℝ≥0∞) ^ (2 : ℝ) * μH[(2 : ℝ)] D := h_lip_img
          _ = 25 * ENNReal.ofReal (16 * r ^ 2) := by rw [h_hd_D, h_five_rpow]
          _ = ENNReal.ofReal 25 * ENNReal.ofReal (16 * r ^ 2) := by
                rw [show (25 : ℝ≥0∞) = ENNReal.ofReal 25 from by
                  rw [ENNReal.ofReal_ofNat]]
          _ = ENNReal.ofReal (400 * r ^ 2) := by
                rw [← ENNReal.ofReal_mul (by norm_num)]
                congr 1
                ring
      have hmeas : MeasurableSet {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1} := by
        have hcont : Continuous fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ :=
          continuous_norm
        exact hcont.measurable (measurableSet_singleton 1)
      have h_restrict_apply :
          ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
              {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1})
            (Metric.closedBall x r) =
          μH[(2 : ℝ)] (Metric.closedBall x r ∩
              {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}) :=
        MeasureTheory.Measure.restrict_apply' hmeas
      rw [h_restrict_apply, ← hcap_def]
      have h_cap_le_img : μH[(2 : ℝ)] cap ≤ μH[(2 : ℝ)] (f '' D) :=
        MeasureTheory.measure_mono h_cap_sub
      have h_400_le_1000 : ENNReal.ofReal (400 * r ^ 2) ≤
          ENNReal.ofReal (1000 * r ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_nonneg r, hr.le]
      exact h_cap_le_img.trans (h_img_le.trans h_400_le_1000)

/-- The geometric bound covering both `r = 0` (handled via `NoAtoms`) and
`r > 0` (handled by `sphere_cap_bound_pos`). -/
lemma sphere_cap_bound
    (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 ≤ r) :
    ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
        {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1})
      (Metric.closedBall x r) ≤ ENNReal.ofReal (1000 * r ^ 2) := by
  rcases hr.lt_or_eq with hpos | hzero
  · exact sphere_cap_bound_pos x r hpos
  · subst hzero
    simp only [Metric.closedBall_zero]
    have h2pos : (0 : ℝ) < 2 := by norm_num
    haveI : MeasureTheory.NoAtoms
        (MeasureTheory.Measure.hausdorffMeasure (2 : ℝ) :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
      MeasureTheory.Measure.noAtoms_hausdorff (X := EuclideanSpace ℝ (Fin 3)) h2pos
    have hsingleton :
        ((MeasureTheory.Measure.hausdorffMeasure (2 : ℝ) :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
          {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}) {x} = 0 := by
      refine le_antisymm ?_ bot_le
      calc ((MeasureTheory.Measure.hausdorffMeasure (2 : ℝ) :
              MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict
            {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1}) {x}
          ≤ (MeasureTheory.Measure.hausdorffMeasure (2 : ℝ) :
              MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) {x} :=
            MeasureTheory.Measure.restrict_apply_le _ _
        _ = 0 := MeasureTheory.measure_singleton x
    rw [hsingleton]
    exact bot_le

/-- (Spherical Frostman.) The 2-dimensional Hausdorff measure restricted to the unit sphere of
`EuclideanSpace ℝ (Fin 3)` is Frostman-regular with exponent `n - 1 = 2`: there is `C_F > 0` with
`(μH[2] ↾ Sphere)(closedBall x r) ≤ ofReal (C_F · r ^ (n - 1))` for every `x` and every `r ≥ 0`. -/
theorem spherical_frostman_two :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ (x : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 ≤ r →
        ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
            {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1})
          (Metric.closedBall x r) ≤ ENNReal.ofReal (C_F * r ^ (3 - 1)) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro x r hr
  have h : ((μH[(2 : ℝ)] : MeasureTheory.Measure _).restrict
        {v : EuclideanSpace ℝ (Fin 3) | ‖v‖ = 1})
      (Metric.closedBall x r) ≤ ENNReal.ofReal (1000 * r ^ 2) :=
    sphere_cap_bound x r hr
  have hpow : r ^ (3 - 1) = r ^ 2 := by norm_num
  rw [hpow]
  exact h

/-- Sup-norm `δ`-cthickening of a segment of length at most one in `Fin 3 → ℝ` has
Lebesgue volume at most `200 · δ²`. This is the `1×δ`-tube volume bound used
for comparison with Euclidean tubes. -/
lemma volume_cthickening_unit_dist_segment_le
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (xpt ypt : Fin 3 → ℝ) (h_dist : dist xpt ypt ≤ 1) :
    MeasureTheory.volume.real
        (Metric.cthickening δ (segment ℝ xpt ypt)) ≤ 200 * δ ^ 2 := by
  classical
  set N : ℕ := ⌈(1 : ℝ) / δ⌉₊ with hN_def
  have hN_pos : 0 < N := by
    rw [hN_def, Nat.lt_ceil]
    simp only [CharP.cast_eq_zero]
    positivity
  have hN_real_pos : (0 : ℝ) < N := by exact_mod_cast hN_pos
  have hN_ge : (1 : ℝ) / δ ≤ N := by
    rw [hN_def]; exact Nat.le_ceil _
  have hN_lt : (N : ℝ) < 1 / δ + 1 := by
    rw [hN_def]; exact Nat.ceil_lt_add_one (by positivity)
  have h_oneOverN_le : (1 : ℝ) / N ≤ δ := by
    rw [div_le_iff₀ hN_real_pos]
    have h_ge_one : 1 ≤ (N : ℝ) * δ := by
      have hmul := mul_le_mul_of_nonneg_right hN_ge hδ_pos.le
      rw [div_mul_cancel₀ _ hδ_pos.ne'] at hmul
      linarith
    linarith
  have h_oneOverN_nn : (0 : ℝ) ≤ 1 / N := by positivity
  have h_two_delta_nn : (0 : ℝ) ≤ 2 * δ := by positivity
  let v : Fin 3 → ℝ := ypt - xpt
  let z : Fin (N + 1) → (Fin 3 → ℝ) := fun k =>
    xpt + ((k : ℝ) / N) • v
  have h_seg_sub : segment ℝ xpt ypt ⊆
      ⋃ k : Fin (N + 1), Metric.closedBall (z k) ((1 : ℝ) / N) := by
    rw [segment_eq_image']
    rintro p ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
    set k0 : ℕ := ⌊θ * N⌋₊ with hk0_def
    have h_k0_bound : k0 ≤ N := by
      rw [hk0_def]
      apply Nat.floor_le_of_le
      have h_le : θ * (N : ℝ) ≤ 1 * N :=
        mul_le_mul_of_nonneg_right hθ₁ hN_real_pos.le
      simp only [one_mul] at h_le
      exact_mod_cast h_le
    have h_k0_lt : k0 < N + 1 := by omega
    let k : Fin (N + 1) := ⟨k0, h_k0_lt⟩
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    change dist (xpt + θ • v) (z k) ≤ 1 / N
    change dist (xpt + θ • v) (xpt + ((k : ℝ) / N) • v) ≤ 1 / N
    have h_k_eq : ((k : ℕ) : ℝ) = k0 := by simp [k]
    rw [h_k_eq]
    have hxv : xpt + θ • v - (xpt + (k0 / N : ℝ) • v) =
        (θ - k0 / N) • v := by
      rw [add_sub_add_left_eq_sub]
      rw [← sub_smul]
    rw [dist_eq_norm, hxv]
    rw [norm_smul, Real.norm_eq_abs]
    have h_v_norm : ‖v‖ ≤ 1 := by
      change ‖ypt - xpt‖ ≤ 1
      rw [← dist_eq_norm, dist_comm]
      exact h_dist
    have h_k0_le : (k0 : ℝ) ≤ θ * N := Nat.floor_le (by positivity)
    have h_k0_gt : θ * N - 1 < k0 := by
      have := Nat.lt_floor_add_one (θ * N)
      linarith
    have h_abs_le : |θ - (k0 : ℝ) / N| ≤ 1 / N := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1 : (k0 : ℝ) / N ≤ θ := by
          rw [div_le_iff₀ hN_real_pos]
          linarith
        linarith
      · rw [sub_le_iff_le_add, ← add_div]
        rw [le_div_iff₀ hN_real_pos]
        linarith
    calc |θ - (k0 : ℝ) / N| * ‖v‖
        ≤ |θ - (k0 : ℝ) / N| * 1 :=
          mul_le_mul_of_nonneg_left h_v_norm (abs_nonneg _)
      _ = |θ - (k0 : ℝ) / N| := mul_one _
      _ ≤ 1 / N := h_abs_le
  have h_seg_compact : IsCompact (segment ℝ xpt ypt) := by
    rw [segment_eq_image']
    refine IsCompact.image isCompact_Icc ?_
    exact continuous_const.add ((continuous_id.smul continuous_const))
  have h_seg_closed : IsClosed (segment ℝ xpt ypt) := h_seg_compact.isClosed
  have h_cthick_sub : Metric.cthickening δ (segment ℝ xpt ypt) ⊆
      ⋃ k : Fin (N + 1), Metric.closedBall (z k) (δ + 1 / N) := by
    rw [h_seg_closed.cthickening_eq_biUnion_closedBall hδ_pos.le]
    intro p hp
    simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hp
    obtain ⟨q, hq_seg, hpq⟩ := hp
    have hq_in_cover := h_seg_sub hq_seg
    rw [Set.mem_iUnion] at hq_in_cover
    obtain ⟨k, hq_in_ball⟩ := hq_in_cover
    rw [Metric.mem_closedBall] at hq_in_ball
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    rw [Metric.mem_closedBall]
    calc dist p (z k)
        ≤ dist p q + dist q (z k) := dist_triangle _ _ _
      _ ≤ δ + 1 / N := add_le_add hpq hq_in_ball
  have h_radius_le : δ + 1 / N ≤ 2 * δ := by linarith
  have h_radius_nn : (0 : ℝ) ≤ δ + 1 / N := by positivity
  have h_enclosed : ∀ k : Fin (N + 1),
      Metric.closedBall (z k) (δ + 1 / N) ⊆ Metric.closedBall (z k) (2 * δ) := by
    intro k
    exact Metric.closedBall_subset_closedBall h_radius_le
  have h_vol_ball : ∀ k : Fin (N + 1),
      MeasureTheory.volume.real (Metric.closedBall (z k) (2 * δ))
        = 64 * δ ^ 3 := by
    intro k
    rw [MeasureTheory.measureReal_def,
        Real.volume_pi_closedBall (z k) h_two_delta_nn,
        ENNReal.toReal_ofReal (by positivity)]
    rw [Fintype.card_fin]
    ring
  have h_full_sub : Metric.cthickening δ (segment ℝ xpt ypt) ⊆
      ⋃ k : Fin (N + 1), Metric.closedBall (z k) (2 * δ) := by
    refine h_cthick_sub.trans ?_
    refine Set.iUnion_mono ?_
    intro k
    exact h_enclosed k
  have h_union_vol_finite :
      MeasureTheory.volume
        (⋃ k : Fin (N + 1), Metric.closedBall (z k) (2 * δ)) ≠ ⊤ := by
    apply ne_of_lt
    calc MeasureTheory.volume
            (⋃ k : Fin (N + 1), Metric.closedBall (z k) (2 * δ))
          ≤ ∑ k : Fin (N + 1),
              MeasureTheory.volume (Metric.closedBall (z k) (2 * δ)) :=
            MeasureTheory.measure_iUnion_fintype_le _ _
      _ < ∞ := by
            apply ENNReal.sum_lt_top.2
            intro i _
            rw [Real.volume_pi_closedBall (z i) h_two_delta_nn]
            exact ENNReal.ofReal_lt_top
  have h_mono : MeasureTheory.volume.real
      (Metric.cthickening δ (segment ℝ xpt ypt)) ≤
      MeasureTheory.volume.real
        (⋃ k : Fin (N + 1), Metric.closedBall (z k) (2 * δ)) :=
    MeasureTheory.measureReal_mono h_full_sub h_union_vol_finite
  have h_sub : MeasureTheory.volume.real
      (⋃ k : Fin (N + 1), Metric.closedBall (z k) (2 * δ)) ≤
      ∑ k : Fin (N + 1),
        MeasureTheory.volume.real (Metric.closedBall (z k) (2 * δ)) :=
    MeasureTheory.measureReal_iUnion_fintype_le _
  have h_sum_eq : ∑ k : Fin (N + 1),
        MeasureTheory.volume.real (Metric.closedBall (z k) (2 * δ))
      = (N + 1 : ℕ) * (64 * δ ^ 3) := by
    rw [show (fun k : Fin (N + 1) =>
        MeasureTheory.volume.real (Metric.closedBall (z k) (2 * δ)))
        = (fun _ => 64 * δ ^ 3) from funext (fun k => h_vol_ball k)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
  have hN1_le : ((N : ℝ) + 1) ≤ 1 / δ + 2 := by linarith
  calc MeasureTheory.volume.real (Metric.cthickening δ (segment ℝ xpt ypt))
      ≤ MeasureTheory.volume.real
          (⋃ k : Fin (N + 1), Metric.closedBall (z k) (2 * δ)) := h_mono
    _ ≤ ∑ k : Fin (N + 1),
          MeasureTheory.volume.real (Metric.closedBall (z k) (2 * δ)) := h_sub
    _ = (N + 1 : ℕ) * (64 * δ ^ 3) := h_sum_eq
    _ = ((N : ℝ) + 1) * (64 * δ ^ 3) := by push_cast; ring
    _ ≤ (1 / δ + 2) * (64 * δ ^ 3) := by
          apply mul_le_mul_of_nonneg_right hN1_le
          positivity
    _ = 64 * δ ^ 2 + 128 * δ ^ 3 := by
          field_simp; ring
    _ ≤ 200 * δ ^ 2 := by
          have hδ2_nn : 0 ≤ δ ^ 2 := sq_nonneg _
          have hδ3_le : δ ^ 3 ≤ δ ^ 2 := by
            have : δ ^ 3 = δ ^ 2 * δ := by ring
            rw [this]
            have : δ ^ 2 * δ ≤ δ ^ 2 * 1 := by
              apply mul_le_mul_of_nonneg_left hδ_le hδ2_nn
            linarith
          nlinarith

/-- Euclidean `δ`-cthickening of a unit segment in three dimensions has volume at most
`200 · δ²`. This follows by mapping it into the corresponding sup-norm thickening. -/
lemma volume_cthickening_unit_dist_segment_le_eucl
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (xpt ypt : EuclideanSpace ℝ (Fin 3)) (h_dist : dist xpt ypt = 1) :
    MeasureTheory.volume.real
        (Metric.cthickening δ (segment ℝ xpt ypt)) ≤ 200 * δ ^ 2 := by
  have h_image_sub :
      toPi '' Metric.cthickening δ (segment ℝ xpt ypt) ⊆
        Metric.cthickening δ (segment ℝ (toPi xpt) (toPi ypt)) := by
    simpa only [image_segment_toPi] using
      image_cthickening_subset δ hδ_pos.le (segment ℝ xpt ypt)
  have h_target_finite : MeasureTheory.volume
      (Metric.cthickening δ (segment ℝ (toPi xpt) (toPi ypt))) ≠ ∞ :=
    (isCompact_segment.cthickening).measure_lt_top.ne
  have h_toPi_dist : dist (toPi xpt) (toPi ypt) ≤ 1 :=
    (dist_toPi_le xpt ypt).trans_eq h_dist
  calc
    MeasureTheory.volume.real (Metric.cthickening δ (segment ℝ xpt ypt))
        = MeasureTheory.volume.real
            (toPi '' Metric.cthickening δ (segment ℝ xpt ypt)) := by
              simp only [MeasureTheory.measureReal_def, volume_image_toPi]
    _ ≤ MeasureTheory.volume.real
          (Metric.cthickening δ (segment ℝ (toPi xpt) (toPi ypt))) :=
      MeasureTheory.measureReal_mono h_image_sub h_target_finite
    _ ≤ 200 * δ ^ 2 :=
      volume_cthickening_unit_dist_segment_le hδ_pos hδ_le _ _ h_toPi_dist

/-- Volume bound for the sup-norm `δ`-thickening of the image of a finite union of Euclidean closed
balls of common radius `2 δ`, transported from `EuclideanSpace ℝ (Fin 3)` to `Fin 3 → ℝ` via
`WithLp.equiv 2`: the volume is at most `400 · #J · δ³`. -/
lemma volume_thickening_union_two_radius_balls
    {ι : Type} (J : Set ι) (hJ : J.Finite)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) (hδ : 0 < δ) :
    MeasureTheory.volume.real
        (Metric.thickening δ
          (((WithLp.equiv 2 (Fin 3 → ℝ)) :
              EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ''
            (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)))) ≤
      400 * (hJ.toFinset.card : ℝ) * δ ^ 3 := by
  classical
  set e : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ) :=
    (WithLp.equiv 2 (Fin 3 → ℝ) :
      EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) with he_def
  have hδ_nn : (0 : ℝ) ≤ δ := hδ.le
  have h3δ_nn : (0 : ℝ) ≤ 3 * δ := by positivity
  have hImageUnion :
      e '' (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)) =
        ⋃ i ∈ J, e '' Metric.closedBall (x i) ((2 : ℝ) * δ) := by
    rw [Set.image_iUnion]
    refine Set.iUnion_congr ?_
    intro i
    rw [Set.image_iUnion]
  have hImageSub : ∀ i : ι,
      e '' Metric.closedBall (x i) ((2 : ℝ) * δ) ⊆
        Metric.closedBall (e (x i)) ((2 : ℝ) * δ) := by
    intro i y hy
    rcases hy with ⟨v, hv, rfl⟩
    simp only [Metric.mem_closedBall] at hv ⊢
    have h_l2 : dist v (x i) ≤ 2 * δ := hv
    have hle : dist (e v) (e (x i)) ≤ dist v (x i) := by
      have h_sup_le_l2 : ∀ j : Fin 3,
          ‖(e v - e (x i)) j‖ ≤ dist v (x i) := by
        intro j
        have heq1 : (e v - e (x i)) j = v j - (x i) j := by
          simp [he_def, Pi.sub_apply]
        rw [heq1]
        have hdist_eq : dist v (x i) = √(∑ k, dist (v k) ((x i) k) ^ 2) :=
          EuclideanSpace.dist_eq v (x i)
        rw [hdist_eq]
        have hj : dist (v j) ((x i) j) ^ 2 ≤
            ∑ k, dist (v k) ((x i) k) ^ 2 := by
          refine Finset.single_le_sum (f := fun k =>
            dist (v k) ((x i) k) ^ 2) ?_ (Finset.mem_univ j)
          intro k _
          exact sq_nonneg _
        have h_abs : ‖v j - (x i) j‖ = dist (v j) ((x i) j) := by
          rw [Real.norm_eq_abs, Real.dist_eq]
        rw [h_abs]
        have hd_nn : (0 : ℝ) ≤ dist (v j) ((x i) j) := dist_nonneg
        calc dist (v j) ((x i) j)
            = √(dist (v j) ((x i) j) ^ 2) := by
              rw [Real.sqrt_sq hd_nn]
          _ ≤ √(∑ k, dist (v k) ((x i) k) ^ 2) :=
              Real.sqrt_le_sqrt hj
      have h_sup_le : ‖e v - e (x i)‖ ≤ dist v (x i) := by
        rw [pi_norm_le_iff_of_nonneg dist_nonneg]
        intro j
        exact h_sup_le_l2 j
      rw [dist_eq_norm]
      exact h_sup_le
    exact hle.trans h_l2
  have hThickUnion :
      Metric.thickening δ
          (⋃ i ∈ J, e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) =
        ⋃ i ∈ J,
          Metric.thickening δ (e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) :=
    Metric.thickening_biUnion δ _ J
  have hThickSub : ∀ i : ι,
      Metric.thickening δ (e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) ⊆
        Metric.closedBall (e (x i)) (3 * δ) := by
    intro i
    have h1 :
        Metric.thickening δ (e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) ⊆
          Metric.thickening δ (Metric.closedBall (e (x i)) ((2 : ℝ) * δ)) :=
      Metric.thickening_subset_of_subset δ (hImageSub i)
    have h2 : Metric.thickening δ (Metric.closedBall (e (x i)) ((2 : ℝ) * δ))
        = Metric.ball (e (x i)) (δ + (2 : ℝ) * δ) :=
      thickening_closedBall hδ (by positivity) (e (x i))
    have h3 : Metric.ball (e (x i)) (δ + (2 : ℝ) * δ) ⊆
        Metric.closedBall (e (x i)) (3 * δ) := by
      intro y hy
      simp only [Metric.mem_ball] at hy
      simp only [Metric.mem_closedBall]
      have : δ + 2 * δ = 3 * δ := by ring
      linarith
    exact h1.trans (by rw [h2]; exact h3)
  have hMainSub :
      Metric.thickening δ
          (e '' (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ))) ⊆
        ⋃ i ∈ J, Metric.closedBall (e (x i)) (3 * δ) := by
    rw [hImageUnion, hThickUnion]
    refine Set.iUnion_subset ?_
    intro i
    refine Set.iUnion_subset ?_
    intro hi
    refine (hThickSub i).trans ?_
    exact Set.subset_biUnion_of_mem (u := fun k => Metric.closedBall (e (x k)) (3 * δ)) hi
  have hUEq :
      (⋃ i ∈ J, Metric.closedBall (e (x i)) (3 * δ)) =
        (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) := by
    ext y
    simp [Set.Finite.mem_toFinset]
  have hVolFinite : MeasureTheory.volume
      (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) ≠ ∞ := by
    apply ne_of_lt
    calc MeasureTheory.volume
            (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ))
          ≤ ∑ i ∈ hJ.toFinset,
              MeasureTheory.volume (Metric.closedBall (e (x i)) (3 * δ)) :=
            MeasureTheory.measure_biUnion_finset_le _ _
      _ < ∞ := by
            apply ENNReal.sum_lt_top.2
            intro i _
            rw [Real.volume_pi_closedBall (e (x i)) h3δ_nn]
            exact ENNReal.ofReal_lt_top
  have hMono : MeasureTheory.volume.real
      (Metric.thickening δ
        (e '' (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)))) ≤
      MeasureTheory.volume.real
        (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) := by
    rw [← hUEq]
    exact MeasureTheory.measureReal_mono hMainSub
      (by rw [hUEq]; exact hVolFinite)
  have hSub : MeasureTheory.volume.real
      (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) ≤
      ∑ i ∈ hJ.toFinset,
        MeasureTheory.volume.real (Metric.closedBall (e (x i)) (3 * δ)) :=
    MeasureTheory.measureReal_biUnion_finset_le _ _
  have hBallVol : ∀ i : ι,
      MeasureTheory.volume.real (Metric.closedBall (e (x i)) (3 * δ))
        = 216 * δ ^ 3 := by
    intro i
    rw [MeasureTheory.measureReal_def, Real.volume_pi_closedBall (e (x i)) h3δ_nn,
        ENNReal.toReal_ofReal]
    · rw [Fintype.card_fin]
      ring_nf
    · positivity
  have hPerBall : ∀ i : ι,
      MeasureTheory.volume.real (Metric.closedBall (e (x i)) (3 * δ))
        ≤ 400 * δ ^ 3 := by
    intro i
    rw [hBallVol i]
    nlinarith [sq_nonneg δ, hδ.le]
  calc MeasureTheory.volume.real
        (Metric.thickening δ
          (e '' (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ))))
      ≤ MeasureTheory.volume.real
          (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) := hMono
    _ ≤ ∑ i ∈ hJ.toFinset,
          MeasureTheory.volume.real (Metric.closedBall (e (x i)) (3 * δ))
        := hSub
    _ ≤ ∑ _i ∈ hJ.toFinset, (400 * δ ^ 3 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact hPerBall i
    _ = (hJ.toFinset.card : ℝ) * (400 * δ ^ 3) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = 400 * (hJ.toFinset.card : ℝ) * δ ^ 3 := by ring

/-- Sibling of `volume_thickening_union_two_radius_balls` exposing the
finiteness witness `volume(thickening) ≠ ⊤`. The geometric content is the
same: the thickening is contained in a finite union of sup-norm closed balls
of radius `3 δ` around the images `e (x i)`, each of finite Lebesgue volume. -/
lemma volume_thickening_union_two_radius_balls_finite
    {ι : Type} (J : Set ι) (hJ : J.Finite)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) (hδ : 0 < δ) :
    MeasureTheory.volume
        (Metric.thickening δ
          (((WithLp.equiv 2 (Fin 3 → ℝ)) :
              EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ''
            (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)))) ≠ ⊤ := by
  classical
  set e : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ) :=
    (WithLp.equiv 2 (Fin 3 → ℝ) :
      EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) with he_def
  have hδ_nn : (0 : ℝ) ≤ δ := hδ.le
  have h3δ_nn : (0 : ℝ) ≤ 3 * δ := by positivity
  have hImageUnion :
      e '' (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)) =
        ⋃ i ∈ J, e '' Metric.closedBall (x i) ((2 : ℝ) * δ) := by
    rw [Set.image_iUnion]
    refine Set.iUnion_congr ?_
    intro i
    rw [Set.image_iUnion]
  have hImageSub : ∀ i : ι,
      e '' Metric.closedBall (x i) ((2 : ℝ) * δ) ⊆
        Metric.closedBall (e (x i)) ((2 : ℝ) * δ) := by
    intro i y hy
    rcases hy with ⟨v, hv, rfl⟩
    simp only [Metric.mem_closedBall] at hv ⊢
    have h_l2 : dist v (x i) ≤ 2 * δ := hv
    have hle : dist (e v) (e (x i)) ≤ dist v (x i) := by
      have h_sup_le_l2 : ∀ j : Fin 3,
          ‖(e v - e (x i)) j‖ ≤ dist v (x i) := by
        intro j
        have heq1 : (e v - e (x i)) j = v j - (x i) j := by
          simp [he_def, Pi.sub_apply]
        rw [heq1]
        have hdist_eq : dist v (x i) = √(∑ k, dist (v k) ((x i) k) ^ 2) :=
          EuclideanSpace.dist_eq v (x i)
        rw [hdist_eq]
        have hj : dist (v j) ((x i) j) ^ 2 ≤
            ∑ k, dist (v k) ((x i) k) ^ 2 := by
          refine Finset.single_le_sum (f := fun k =>
            dist (v k) ((x i) k) ^ 2) ?_ (Finset.mem_univ j)
          intro k _
          exact sq_nonneg _
        have h_abs : ‖v j - (x i) j‖ = dist (v j) ((x i) j) := by
          rw [Real.norm_eq_abs, Real.dist_eq]
        rw [h_abs]
        have hd_nn : (0 : ℝ) ≤ dist (v j) ((x i) j) := dist_nonneg
        calc dist (v j) ((x i) j)
            = √(dist (v j) ((x i) j) ^ 2) := by
              rw [Real.sqrt_sq hd_nn]
          _ ≤ √(∑ k, dist (v k) ((x i) k) ^ 2) :=
              Real.sqrt_le_sqrt hj
      have h_sup_le : ‖e v - e (x i)‖ ≤ dist v (x i) := by
        rw [pi_norm_le_iff_of_nonneg dist_nonneg]
        intro j
        exact h_sup_le_l2 j
      rw [dist_eq_norm]
      exact h_sup_le
    exact hle.trans h_l2
  have hThickUnion :
      Metric.thickening δ
          (⋃ i ∈ J, e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) =
        ⋃ i ∈ J,
          Metric.thickening δ (e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) :=
    Metric.thickening_biUnion δ _ J
  have hThickSub : ∀ i : ι,
      Metric.thickening δ (e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) ⊆
        Metric.closedBall (e (x i)) (3 * δ) := by
    intro i
    have h1 :
        Metric.thickening δ (e '' Metric.closedBall (x i) ((2 : ℝ) * δ)) ⊆
          Metric.thickening δ (Metric.closedBall (e (x i)) ((2 : ℝ) * δ)) :=
      Metric.thickening_subset_of_subset δ (hImageSub i)
    have h2 : Metric.thickening δ (Metric.closedBall (e (x i)) ((2 : ℝ) * δ))
        = Metric.ball (e (x i)) (δ + (2 : ℝ) * δ) :=
      thickening_closedBall hδ (by positivity) (e (x i))
    have h3 : Metric.ball (e (x i)) (δ + (2 : ℝ) * δ) ⊆
        Metric.closedBall (e (x i)) (3 * δ) := by
      intro y hy
      simp only [Metric.mem_ball] at hy
      simp only [Metric.mem_closedBall]
      have : δ + 2 * δ = 3 * δ := by ring
      linarith
    exact h1.trans (by rw [h2]; exact h3)
  have hMainSub :
      Metric.thickening δ
          (e '' (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ))) ⊆
        ⋃ i ∈ J, Metric.closedBall (e (x i)) (3 * δ) := by
    rw [hImageUnion, hThickUnion]
    refine Set.iUnion_subset ?_
    intro i
    refine Set.iUnion_subset ?_
    intro hi
    refine (hThickSub i).trans ?_
    exact Set.subset_biUnion_of_mem (u := fun k => Metric.closedBall (e (x k)) (3 * δ)) hi
  have hUEq :
      (⋃ i ∈ J, Metric.closedBall (e (x i)) (3 * δ)) =
        (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) := by
    ext y
    simp [Set.Finite.mem_toFinset]
  have hVolFinite : MeasureTheory.volume
      (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) ≠ ∞ := by
    apply ne_of_lt
    calc MeasureTheory.volume
            (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ))
          ≤ ∑ i ∈ hJ.toFinset,
              MeasureTheory.volume (Metric.closedBall (e (x i)) (3 * δ)) :=
            MeasureTheory.measure_biUnion_finset_le _ _
      _ < ∞ := by
            apply ENNReal.sum_lt_top.2
            intro i _
            rw [Real.volume_pi_closedBall (e (x i)) h3δ_nn]
            exact ENNReal.ofReal_lt_top
  have hMonoMeas : MeasureTheory.volume
      (Metric.thickening δ
        (e '' (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)))) ≤
      MeasureTheory.volume
        (⋃ i ∈ hJ.toFinset, Metric.closedBall (e (x i)) (3 * δ)) := by
    rw [← hUEq]
    exact MeasureTheory.measure_mono hMainSub
  exact ne_top_of_le_ne_top hVolFinite hMonoMeas

/-- Euclidean version of `volume_thickening_union_two_radius_balls`. The Euclidean
thickening maps into the sup-norm thickening used by that lemma. -/
lemma volume_thickening_union_two_radius_balls_eucl
    {ι : Type} (J : Set ι) (hJ : J.Finite)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) (hδ : 0 < δ) :
    MeasureTheory.volume.real
        (Metric.thickening δ
          (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ))) ≤
      400 * (hJ.toFinset.card : ℝ) * δ ^ 3 := by
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    ⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)
  have h_toPi : (toPi : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) =
      (WithLp.equiv 2 (Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) := by
    funext y
    rfl
  have h_image_sub : toPi '' Metric.thickening δ U ⊆
      Metric.thickening δ (toPi '' U) := image_thickening_subset δ U
  have h_target_finite : MeasureTheory.volume (Metric.thickening δ (toPi '' U)) ≠ ∞ := by
    rw [h_toPi]
    simpa only [U] using
      volume_thickening_union_two_radius_balls_finite J hJ x δ hδ
  calc
    MeasureTheory.volume.real (Metric.thickening δ U) =
        MeasureTheory.volume.real (toPi '' Metric.thickening δ U) := by
      simp only [MeasureTheory.measureReal_def, volume_image_toPi]
    _ ≤ MeasureTheory.volume.real (Metric.thickening δ (toPi '' U)) :=
      MeasureTheory.measureReal_mono h_image_sub h_target_finite
    _ ≤ 400 * (hJ.toFinset.card : ℝ) * δ ^ 3 := by
      rw [h_toPi]
      simpa only [U] using
        volume_thickening_union_two_radius_balls J hJ x δ hδ

/-- The Euclidean thickening of a finite union of radius-`2δ` balls has finite volume. -/
lemma volume_thickening_union_two_radius_balls_finite_eucl
    {ι : Type} (J : Set ι) (hJ : J.Finite)
    (x : ι → EuclideanSpace ℝ (Fin 3)) (δ : ℝ) (hδ : 0 < δ) :
    MeasureTheory.volume
        (Metric.thickening δ
          (⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ))) ≠ ⊤ := by
  let U : Set (EuclideanSpace ℝ (Fin 3)) :=
    ⋃ i ∈ J, Metric.closedBall (x i) ((2 : ℝ) * δ)
  have h_toPi : (toPi : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) =
      (WithLp.equiv 2 (Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) := by
    funext y
    rfl
  have h_image_sub : toPi '' Metric.thickening δ U ⊆
      Metric.thickening δ (toPi '' U) := image_thickening_subset δ U
  have h_target_finite : MeasureTheory.volume (Metric.thickening δ (toPi '' U)) ≠ ∞ := by
    rw [h_toPi]
    simpa only [U] using
      volume_thickening_union_two_radius_balls_finite J hJ x δ hδ
  have h_image_finite : MeasureTheory.volume (toPi '' Metric.thickening δ U) ≠ ∞ :=
    ne_top_of_le_ne_top h_target_finite (MeasureTheory.measure_mono h_image_sub)
  simpa only [volume_image_toPi] using h_image_finite

end Kakeya.IsBesicovitch
