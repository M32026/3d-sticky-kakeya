import MyLeanRepo.Kakeya.Hairbrush.Basic
import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Hairbrush.Helpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Plane covering by direction-angle bins

Given a central tube T and a family F_σ of tubes at angle [σ, 2σ] from T,
partition F_σ into K = O(σ/δ) bins such that each bin lies in a 2-plane
neighborhood: all tube directions have |inner U.direction n_k| ≤ 2δ for
some unit normal n_k.

Construction:
1. ONB e0=T.direction, e1, e2 via Householder reflection
2. Project each U.direction onto e0⊥, compute angle φ_U via arccos
3. Bin by angle with width δ/σ
4. For bin k, normal n_k is perpendicular to the center direction
5. |inner U.direction n_k| ≤ ‖p_U‖ * (δ/σ) ≤ 2σ * (δ/σ) = 2δ
-/

noncomputable section

open MeasureTheory Metric Set Finset Real
open scoped Classical

namespace Kakeya.Assouad

variable {δ : ℝ}

local instance : DecidableEq (Kakeya.DeltaTube δ) := Classical.decEq _

/-- Angle in [0, 2π) from Cartesian coordinates (x, y). -/
def angleOfCoords (x y : ℝ) : ℝ :=
  if 0 ≤ y then Real.arccos (x / Real.sqrt (x^2 + y^2))
  else 2 * Real.pi - Real.arccos (x / Real.sqrt (x^2 + y^2))

/-- Properties of `angleOfCoords`: range and cosine/sine values. -/
lemma angleOfCoords_spec (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    0 ≤ angleOfCoords x y ∧ angleOfCoords x y < 2 * Real.pi ∧
    Real.cos (angleOfCoords x y) = x / Real.sqrt (x^2 + y^2) ∧
    Real.sin (angleOfCoords x y) = y / Real.sqrt (x^2 + y^2) := by
  set r : ℝ := Real.sqrt (x^2 + y^2) with hr_def
  have h1_pos : 0 < x^2 + y^2 := by
    cases h with
    | inl hx =>
      have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx
      exact add_pos_of_pos_of_nonneg hx2 (by positivity)
    | inr hy =>
      have hy2 : 0 < y^2 := sq_pos_of_ne_zero hy
      exact add_pos_of_nonneg_of_pos (by positivity) hy2
  have hr_pos : 0 < r := Real.sqrt_pos.mpr h1_pos
  have hr2 : r^2 = x^2 + y^2 := by
    rw [hr_def, Real.sq_sqrt (by nlinarith)]
  have h_abs_x_le : |x| ≤ r := by
    have h : x^2 ≤ r^2 := by nlinarith
    have h' : |x|^2 ≤ r^2 := by simpa [sq_abs] using h
    have h'' : |x| ≤ r := by nlinarith [abs_nonneg x, hr_pos]
    exact h''
  have hxr1 : -1 ≤ x / r := by
    have h : -r ≤ x := by linarith [abs_le.mp h_abs_x_le]
    have h' : -1 ≤ x / r := by
      calc -1 = (-r) / r := by field_simp [hr_pos.ne'] <;> ring
        _ ≤ x / r := by gcongr
    exact h'
  have hxr2 : x / r ≤ 1 := by
    have h : x ≤ r := by linarith [abs_le.mp h_abs_x_le]
    have h' : x / r ≤ 1 := by
      calc x / r ≤ r / r := by gcongr
        _ = 1 := by field_simp [hr_pos.ne']
    exact h'
  set φ : ℝ := Real.arccos (x / r) with hφ_def
  have hφ_nonneg : 0 ≤ φ := Real.arccos_nonneg (x / r)
  have hφ_le_pi : φ ≤ Real.pi := Real.arccos_le_pi (x / r)
  have hcos_φ : Real.cos φ = x / r := Real.cos_arccos hxr1 hxr2
  have hsin_φ2 : Real.sin φ = |y| / r := by
    have h : Real.sin φ = Real.sqrt (1 - (x / r)^2) := Real.sin_arccos (x / r)
    rw [h]
    have h2 : 1 - (x / r)^2 = y^2 / r^2 := by
      field_simp [hr_pos.ne'] <;> nlinarith
    rw [h2]
    have h3 : Real.sqrt (y^2 / r^2) = |y| / r := by
      have h4 : Real.sqrt (y^2 / r^2) = Real.sqrt (y^2) / Real.sqrt (r^2) := by
        rw [Real.sqrt_div (by positivity)]
      rw [h4]
      have h5 : Real.sqrt (y^2) = |y| := by
        exact sqrt_sq_eq_abs y
      have h6 : Real.sqrt (r^2) = r := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
      rw [h5, h6]
    exact h3
  by_cases hy : 0 ≤ y
  · -- Case y ≥ 0
    have h_angle : angleOfCoords x y = φ := by
      simp only [angleOfCoords, hy, if_true]
      <;> rfl
    rw [h_angle]
    have h_abs : |y| = y := abs_of_nonneg hy
    exact ⟨hφ_nonneg, by linarith [Real.pi_pos], hcos_φ, by rw [hsin_φ2, h_abs]⟩
  · -- Case y < 0
    have hy' : y < 0 := by linarith
    have h_angle : angleOfCoords x y = 2 * Real.pi - φ := by
      have hny : ¬(0 ≤ y) := by linarith
      simp only [angleOfCoords, hny, if_false] <;> rfl
    rw [h_angle]
    have hφ_pos : 0 < φ := by
      have h_y2_pos : 0 < y^2 := by nlinarith
      have h_x_lt_r : x < r := by
        have h : x^2 < r^2 := by nlinarith
        nlinarith [abs_nonneg x]
      have h_xr_lt_one : x / r < 1 := by
        calc x / r < r / r := by gcongr
          _ = 1 := by field_simp [hr_pos.ne']
      have h : Real.arccos 1 < Real.arccos (x / r) :=
        Real.arccos_lt_arccos hxr1 h_xr_lt_one (by norm_num)
      have h_arccos1 : Real.arccos 1 = 0 := by rw [Real.arccos_one]
      rw [h_arccos1] at h
      exact h
    have h_abs : |y| = -y := abs_of_neg hy'
    constructor
    · linarith
    · constructor
      · linarith
      · constructor
        · have h : Real.cos (2 * Real.pi - φ) = Real.cos φ := by
            rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi] <;> ring
          rw [h, hcos_φ]
        · have h : Real.sin (2 * Real.pi - φ) = -Real.sin φ := by
            rw [Real.sin_sub, Real.sin_two_pi, Real.cos_two_pi] <;> ring
          rw [h, hsin_φ2, h_abs] <;> ring

/--
Plane covering with direction-angle bins (properties 1-3 only).

Produces K bins covering F_σ, each with a normal n_k such that
|inner U.direction n_k| ≤ 2δ for all U in bin k.
-/
lemma plane_covering_basic
    {δ : ℝ} (hδ : 0 < δ)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (T : Kakeya.DeltaTube δ) (F_σ : Kakeya.TubeFamily δ)
    (hFσ_angle : ∀ U ∈ F_σ, σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ) :
    ∃ (K : ℕ) (bins : Fin K → Kakeya.TubeFamily δ),
      (K : ℝ) ≤ 2 * Real.pi * σ / δ + 1 ∧
      (∀ k, bins k ⊆ F_σ) ∧
      (∀ U ∈ F_σ, ∃ k, U ∈ bins k) ∧
      (∀ k, ∃ (n : Point3), ‖n‖ = 1 ∧ ∀ U ∈ bins k, |inner ℝ U.direction n| ≤ 2 * δ) := by
  -- ======================================================================
  -- Build ONB: e0 = T.direction, e1, e2 via Householder reflection
  -- ======================================================================
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1_std : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2_std : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0_std))ᗮ
  have hA : A T.direction = e0_std :=
    Submodule.reflection_sub (by rw [T.direction_unit]; simp [e0_std])
  let e1 : Point3 := A.symm e1_std
  let e2 : Point3 := A.symm e2_std
  have hA_e1 : A e1 = e1_std := by simp [e1]
  have hA_e2 : A e2 = e2_std := by simp [e2]
  have he1_norm : ‖e1‖ = 1 := by
    have h : ‖e1‖ = ‖e1_std‖ := A.symm.norm_map e1_std
    rw [h] <;> simp [e1_std]
  have he2_norm : ‖e2‖ = 1 := by
    have h : ‖e2‖ = ‖e2_std‖ := A.symm.norm_map e2_std
    rw [h] <;> simp [e2_std]
  have h_perp01 : inner ℝ T.direction e1 = 0 := by
    have h : inner ℝ T.direction e1 = inner ℝ (A T.direction) (A e1) :=
      (A.inner_map_map T.direction e1).symm
    rw [h, hA, hA_e1]
    have h_zero : inner ℝ e0_std e1_std = 0 := by
      have h2 : inner ℝ e0_std e1_std = (1 : ℝ) * e0_std 1 :=
        EuclideanSpace.inner_single_right 1 (1 : ℝ) e0_std
      rw [h2]
      have h3 : e0_std 1 = 0 := by simp [e0_std, PiLp.single_apply] <;> decide
      rw [h3] <;> ring
    exact h_zero
  have h_perp02 : inner ℝ T.direction e2 = 0 := by
    have h : inner ℝ T.direction e2 = inner ℝ (A T.direction) (A e2) :=
      (A.inner_map_map T.direction e2).symm
    rw [h, hA, hA_e2]
    have h_zero : inner ℝ e0_std e2_std = 0 := by
      have h2 : inner ℝ e0_std e2_std = (1 : ℝ) * e0_std 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) e0_std
      rw [h2]
      have h3 : e0_std 2 = 0 := by simp [e0_std, PiLp.single_apply] <;> decide
      rw [h3] <;> ring
    exact h_zero
  have h_perp12 : inner ℝ e1 e2 = 0 := by
    have h : inner ℝ e1 e2 = inner ℝ (A e1) (A e2) := (A.inner_map_map e1 e2).symm
    rw [h, hA_e1, hA_e2]
    have h_zero : inner ℝ e1_std e2_std = 0 := by
      have h2 : inner ℝ e1_std e2_std = (1 : ℝ) * e1_std 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) e1_std
      rw [h2]
      have h3 : e1_std 2 = 0 := by simp [e1_std, PiLp.single_apply] <;> decide
      rw [h3] <;> ring
    exact h_zero

  -- Coordinate formulas for the Householder isometry
  have hcoord0 : ∀ (z : Point3), (A z) 0 = inner ℝ z T.direction := by
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
    have h6 : A.symm e0_std = T.direction := by
      have h7 : A (A.symm e0_std) = A T.direction := by rw [A.apply_symm_apply, hA]
      exact A.injective h7
    rw [h6]
  have hcoord1 : ∀ (z : Point3), (A z) 1 = inner ℝ z e1 := by
    intro z
    have h : (A z) 1 = inner ℝ (A z) e1_std := by
      have h2 : inner ℝ (A z) e1_std = (1 : ℝ) * (A z) 1 :=
        EuclideanSpace.inner_single_right 1 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e1_std = inner ℝ z (A.symm e1_std) := by
      have h4 := A.inner_map_map z (A.symm e1_std)
      have h5 : A (A.symm e1_std) = e1_std := A.apply_symm_apply e1_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl
  have hcoord2 : ∀ (z : Point3), (A z) 2 = inner ℝ z e2 := by
    intro z
    have h : (A z) 2 = inner ℝ (A z) e2_std := by
      have h2 : inner ℝ (A z) e2_std = (1 : ℝ) * (A z) 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e2_std = inner ℝ z (A.symm e2_std) := by
      have h4 := A.inner_map_map z (A.symm e2_std)
      have h5 : A (A.symm e2_std) = e2_std := A.apply_symm_apply e2_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl

  -- ======================================================================
  -- Bin parameters
  -- ======================================================================
  let bin_width : ℝ := δ / σ
  have hbw_pos : 0 < bin_width := by positivity
  let K : ℕ := Nat.ceil (2 * Real.pi / bin_width)
  have hK_pos : 0 < K := by
    apply Nat.ceil_pos.mpr
    positivity
  have hK_bound : (K : ℝ) * bin_width ≥ 2 * Real.pi := by
    have h : (K : ℝ) ≥ 2 * Real.pi / bin_width := Nat.le_ceil _
    have h' : (K : ℝ) * bin_width ≥ (2 * Real.pi / bin_width) * bin_width := by gcongr
    have h'' : (2 * Real.pi / bin_width) * bin_width = 2 * Real.pi := by
      field_simp [hbw_pos.ne'] <;> ring
    rw [h''] at h'
    exact h'

  -- ======================================================================
  -- Define bins using angleOfCoords
  -- ======================================================================
  let angle_for (U : Kakeya.DeltaTube δ) : ℝ :=
    angleOfCoords (inner ℝ U.direction e1) (inner ℝ U.direction e2)

  let bins : Fin K → Kakeya.TubeFamily δ := fun k =>
    Finset.filter (fun U =>
      let φ' := angle_for U
      (k : ℝ) * bin_width ≤ φ' ∧ φ' < (k + 1 : ℝ) * bin_width
    ) F_σ

  -- Property 1: subset
  have h_sub : ∀ k, bins k ⊆ F_σ := by
    intro k
    exact Finset.filter_subset _ _

  -- Helper: for U ∈ F_σ, the projection coordinates are nonzero
  have h_coords_nonzero : ∀ U ∈ F_σ,
      (inner ℝ U.direction e1 ≠ 0 ∨ inner ℝ U.direction e2 ≠ 0) := by
    intro U hU
    let c : ℝ := inner ℝ T.direction U.direction
    let p_U : Point3 := U.direction - c • T.direction
    have h_angle_U : σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ := hFσ_angle U hU
    let θ : ℝ := angleBetween T U
    have hθ1 : σ ≤ θ := h_angle_U.1
    have hθ2 : θ ≤ 2 * σ := h_angle_U.2
    have hθ_pos : 0 < θ := by linarith
    have hθ_lt_pi : θ < Real.pi := by
      have h : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      linarith
    have h_bound1 : -1 ≤ c := by
      have h_inner : inner ℝ T.direction U.direction = c := rfl
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by
        rw [←h_inner] <;> simpa using h
      exact (abs_le.mp h').1
    have h_bound2 : c ≤ 1 := by
      have h_inner : inner ℝ T.direction U.direction = c := rfl
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by
        rw [←h_inner] <;> simpa using h
      exact (abs_le.mp h').2
    have hcosθ : Real.cos θ = c := by
      have h_eq : θ = Real.arccos c := by rfl
      rw [h_eq]
      exact Real.cos_arccos h_bound1 h_bound2
    have hpU_norm2 : ‖p_U‖ ^ 2 = Real.sin θ ^ 2 := by
      have h_norm : ‖p_U‖ ^ 2 = ‖U.direction‖ ^ 2 - 2 * inner ℝ U.direction (c • T.direction) + ‖c • T.direction‖ ^ 2 :=
        norm_sub_sq_real U.direction (c • T.direction)
      have h_inner1 : inner ℝ U.direction (c • T.direction) = c^2 := by
        rw [inner_smul_right]
        have h_comm : inner ℝ U.direction T.direction = inner ℝ T.direction U.direction :=
          (real_inner_comm U.direction T.direction).symm
        rw [h_comm] <;> ring
      have h_norm2 : ‖c • T.direction‖ ^ 2 = c^2 := by
        simp [norm_smul, T.direction_unit] <;> ring
      have h_main : ‖p_U‖ ^ 2 = 1 - c^2 := by
        rw [h_norm, h_inner1, h_norm2, U.direction_unit] <;> ring
      have h_sin2 : 1 - c^2 = Real.sin θ ^ 2 := by
        have h4 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
        have h5 : Real.cos θ = c := hcosθ
        rw [h5] at h4
        linarith
      rw [h_main, h_sin2]
    have hpU_pos : 0 < ‖p_U‖ := by
      have h_sin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
      nlinarith [hpU_norm2, norm_nonneg p_U]
    by_contra h'
    push Not at h'
    have hx : inner ℝ U.direction e1 = 0 := h'.1
    have hy : inner ℝ U.direction e2 = 0 := h'.2
    have h_pe1 : inner ℝ p_U e1 = 0 := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, h_perp01, hx] <;> ring
    have h_pe2 : inner ℝ p_U e2 = 0 := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, h_perp02, hy] <;> ring
    have h_pT : inner ℝ p_U T.direction = 0 := by
      dsimp only [p_U]
      have h1 : inner ℝ (U.direction - c • T.direction) T.direction =
          inner ℝ U.direction T.direction - inner ℝ (c • T.direction) T.direction :=
        inner_sub_left U.direction (c • T.direction) T.direction
      rw [h1]
      have h2 : inner ℝ (c • T.direction) T.direction = c * inner ℝ T.direction T.direction := by
        exact inner_smul_left T.direction T.direction (r := c)
      rw [h2]
      have h_comm : inner ℝ U.direction T.direction = c := by
        exact (real_inner_comm U.direction T.direction).symm
      rw [h_comm]
      have hTt : inner ℝ T.direction T.direction = 1 := by
        have h : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
          exact real_inner_self_eq_norm_sq T.direction
        rw [h, T.direction_unit] <;> norm_num
      rw [hTt] <;> ring
    have h_ApU0 : (A p_U) 0 = 0 := by rw [hcoord0 p_U, h_pT]
    have h_ApU1 : (A p_U) 1 = 0 := by rw [hcoord1 p_U, h_pe1]
    have h_ApU2 : (A p_U) 2 = 0 := by rw [hcoord2 p_U, h_pe2]
    have h_ApU_eq_zero : A p_U = 0 := by
      ext i
      fin_cases i <;> tauto
    have h_pU_eq_zero : p_U = 0 := by
      have h : A p_U = A (0 : Point3) := by rw [h_ApU_eq_zero] <;> simp
      exact A.injective h
    rw [h_pU_eq_zero] at hpU_pos
    <;> simp at hpU_pos <;> linarith

  -- Property 2: covering
  have h_cover : ∀ U ∈ F_σ, ∃ (k : Fin K), U ∈ bins k := by
    intro U hU
    let x := inner ℝ U.direction e1
    let y := inner ℝ U.direction e2
    have h_ne_zero : x ≠ 0 ∨ y ≠ 0 := h_coords_nonzero U hU
    let φ' := angle_for U
    have hspec := angleOfCoords_spec x y h_ne_zero
    have hφ'_nonneg : 0 ≤ φ' := hspec.1
    have hφ'_lt_2pi : φ' < 2 * Real.pi := hspec.2.1
    let k : ℕ := Nat.floor (φ' / bin_width)
    have hk1 : (k : ℝ) ≤ φ' / bin_width := Nat.floor_le (ha := by positivity)
    have hk2 : φ' / bin_width < (k : ℝ) + 1 := Nat.lt_floor_add_one (φ' / bin_width)
    have hk3 : (k : ℝ) * bin_width ≤ φ' := by
      calc (k : ℝ) * bin_width ≤ (φ' / bin_width) * bin_width := by gcongr
        _ = φ' := by field_simp [hbw_pos.ne'] <;> ring
    have hk4 : φ' < ((k : ℝ) + 1) * bin_width := by
      calc φ' = (φ' / bin_width) * bin_width := by field_simp [hbw_pos.ne'] <;> ring
        _ < ((k : ℝ) + 1) * bin_width := by gcongr
    have hk_lt_K : k < K := by
      have h : φ' / bin_width < (K : ℝ) := by
        calc φ' / bin_width < (2 * Real.pi) / bin_width := by gcongr
          _ ≤ (K : ℝ) := by
            have h5 : (K : ℝ) ≥ 2 * Real.pi / bin_width := Nat.le_ceil _
            exact h5
      have h6 : (k : ℝ) < (K : ℝ) := by linarith [hk1]
      exact_mod_cast h6
    let k' : Fin K := ⟨k, hk_lt_K⟩
    have hU_in : U ∈ bins k' := by
      simp only [bins, Finset.mem_filter]
      exact ⟨hU, hk3, hk4⟩
    exact ⟨k', hU_in⟩

  -- Property 3: plane neighborhood
  have h_plane : ∀ (k : Fin K), ∃ (n : Point3), ‖n‖ = 1 ∧
      ∀ U ∈ bins k, |inner ℝ U.direction n| ≤ 2 * δ := by
    intro k
    let α : ℝ := (k : ℝ) * bin_width
    let n : Point3 := -Real.sin α • e1 + Real.cos α • e2

    let n_std : Point3 := -Real.sin α • e1_std + Real.cos α • e2_std
    have h_n_def : n = A.symm n_std := by
      simp [n, n_std, e1, e2] <;> abel
    have hn_norm : ‖n‖ = 1 := by
      rw [h_n_def]
      have h : ‖A.symm n_std‖ = ‖n_std‖ := A.symm.norm_map n_std
      rw [h]
      have h2 : ‖n_std‖ ^ 2 = ∑ i : Fin 3, (n_std i)^2 := EuclideanSpace.real_norm_sq_eq n_std
      have h3 : n_std 0 = 0 := by
        simp [n_std, e1_std, e2_std, PiLp.single_apply]
      have h4 : n_std 1 = -Real.sin α := by
        simp [n_std, e1_std, e2_std, PiLp.single_apply]
      have h5 : n_std 2 = Real.cos α := by
        simp [n_std, e1_std, e2_std, PiLp.single_apply]
      have h6 : ‖n_std‖ ^ 2 = 1 := by
        have h_sum : ∑ i : Fin 3, (n_std i)^2 = (n_std 0)^2 + (n_std 1)^2 + (n_std 2)^2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h2, h_sum, h3, h4, h5]
        have h7 : (0 : ℝ)^2 + (-Real.sin α)^2 + (Real.cos α)^2 = 1 := by
          have h8 := Real.sin_sq_add_cos_sq α
          nlinarith
        exact h7
      have h9 : 0 ≤ ‖n_std‖ := by positivity
      nlinarith

    refine ⟨n, hn_norm, ?_⟩
    intro U hU
    have hU_Fσ : U ∈ F_σ := h_sub k hU
    have h_angle_U : σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ := hFσ_angle U hU_Fσ
    let θ : ℝ := angleBetween T U
    have hθ1 : σ ≤ θ := h_angle_U.1
    have hθ2 : θ ≤ 2 * σ := h_angle_U.2
    have hθ_pos : 0 < θ := by linarith
    have hθ_lt_pi : θ < Real.pi := by
      have h : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      linarith

    let x : ℝ := inner ℝ U.direction e1
    let y : ℝ := inner ℝ U.direction e2
    let φ' := angle_for U
    have hbin : (k : ℝ) * bin_width ≤ φ' ∧ φ' < (k + 1 : ℝ) * bin_width := by
      simp only [bins, Finset.mem_filter] at hU
      exact hU.2
    let Δφ : ℝ := φ' - α
    have hΔφ_nonneg : 0 ≤ Δφ := by linarith
    have hΔφ_lt : Δφ < bin_width := by linarith

    -- Projection of U.direction onto T.directionᗮ
    let c : ℝ := inner ℝ T.direction U.direction
    let p_U : Point3 := U.direction - c • T.direction

    have h_bound1 : -1 ≤ c := by
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by simpa [c] using h
      exact (abs_le.mp h').1
    have h_bound2 : c ≤ 1 := by
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by simpa [c] using h
      exact (abs_le.mp h').2
    have hcosθ : Real.cos θ = c := by
      have h_eq : θ = Real.arccos c := by rfl
      rw [h_eq]
      exact Real.cos_arccos h_bound1 h_bound2

    have hpU_norm2 : ‖p_U‖ ^ 2 = Real.sin θ ^ 2 := by
      have h_norm : ‖p_U‖ ^ 2 = ‖U.direction‖ ^ 2 - 2 * inner ℝ U.direction (c • T.direction) + ‖c • T.direction‖ ^ 2 :=
        norm_sub_sq_real U.direction (c • T.direction)
      have h_inner1 : inner ℝ U.direction (c • T.direction) = c^2 := by
        rw [inner_smul_right]
        have h_comm : inner ℝ U.direction T.direction = inner ℝ T.direction U.direction :=
          (real_inner_comm U.direction T.direction).symm
        rw [h_comm] <;> ring
      have h_norm2 : ‖c • T.direction‖ ^ 2 = c^2 := by
        simp [norm_smul, T.direction_unit] <;> ring
      have h_main : ‖p_U‖ ^ 2 = 1 - c^2 := by
        rw [h_norm, h_inner1, h_norm2, U.direction_unit] <;> ring
      have h_sin2 : 1 - c^2 = Real.sin θ ^ 2 := by
        have h4 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
        have h5 : Real.cos θ = c := hcosθ
        rw [h5] at h4
        linarith
      rw [h_main, h_sin2]
    have hpU_pos : 0 < ‖p_U‖ := by
      have h_sin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
      have h_pos2 : 0 < ‖p_U‖ ^ 2 := by
        rw [hpU_norm2]; exact sq_pos_of_pos h_sin_pos
      have h_ne : ‖p_U‖ ≠ 0 := sq_pos_iff.mp h_pos2
      have h_nonneg : 0 ≤ ‖p_U‖ := by positivity
      exact h_nonneg.lt_of_ne h_ne.symm
    have hpU_norm : ‖p_U‖ = Real.sin θ := by
      have h1 : 0 ≤ ‖p_U‖ := by positivity
      have h2 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
      exact (sq_eq_sq₀ h1 h2).mp hpU_norm2
    have hpU_le_2σ : ‖p_U‖ ≤ 2 * σ := by
      rw [hpU_norm]
      have h : Real.sin θ ≤ θ := Real.sin_le (by linarith)
      linarith

    -- Coordinates of p_U in (e1,e2) basis
    have hx_eq : inner ℝ p_U e1 = x := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, h_perp01] <;> ring
    have hy_eq : inner ℝ p_U e2 = y := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, h_perp02] <;> ring

    -- p_U coordinates sum to norm squared
    have h_pT : inner ℝ p_U T.direction = 0 := by
      dsimp only [p_U]
      have h1 : inner ℝ (U.direction - c • T.direction) T.direction =
          inner ℝ U.direction T.direction - inner ℝ (c • T.direction) T.direction :=
        inner_sub_left U.direction (c • T.direction) T.direction
      rw [h1]
      have h2 : inner ℝ (c • T.direction) T.direction = c * inner ℝ T.direction T.direction := by
        exact inner_smul_left T.direction T.direction (r := c)
      rw [h2]
      have h_comm : inner ℝ U.direction T.direction = c := by
        exact (real_inner_comm U.direction T.direction).symm
      rw [h_comm]
      have hTt : inner ℝ T.direction T.direction = 1 := by
        have h : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
          exact real_inner_self_eq_norm_sq T.direction
        rw [h, T.direction_unit] <;> norm_num
      rw [hTt] <;> ring
    have hxy_sum : x ^ 2 + y ^ 2 = ‖p_U‖ ^ 2 := by
      have h_norm2 : ‖p_U‖ ^ 2 = ‖A p_U‖ ^ 2 := by
        exact A.norm_map p_U ▸ rfl
      have h_ApU0 : (A p_U) 0 = 0 := by rw [hcoord0 p_U, h_pT]
      have h_ApU1 : (A p_U) 1 = x := by rw [hcoord1 p_U, hx_eq]
      have h_ApU2 : (A p_U) 2 = y := by rw [hcoord2 p_U, hy_eq]
      have h_sum : ‖A p_U‖ ^ 2 = (A p_U 0)^2 + (A p_U 1)^2 + (A p_U 2)^2 := by
        have h : ‖A p_U‖ ^ 2 = ∑ i : Fin 3, ((A p_U) i)^2 := EuclideanSpace.real_norm_sq_eq (A p_U)
        rw [h]
        simp [Fin.sum_univ_succ] <;> ring
      rw [h_norm2, h_sum, h_ApU0, h_ApU1, h_ApU2] <;> ring

    have h_ne_zero : x ≠ 0 ∨ y ≠ 0 := h_coords_nonzero U hU_Fσ

    -- cos and sin of angle_for
    have hspec := angleOfCoords_spec x y h_ne_zero
    have hcos_φ' : Real.cos φ' = x / Real.sqrt (x^2 + y^2) := hspec.2.2.1
    have hsin_φ' : Real.sin φ' = y / Real.sqrt (x^2 + y^2) := hspec.2.2.2
    have h_r_eq : Real.sqrt (x^2 + y^2) = ‖p_U‖ := by
      have h : x^2 + y^2 = ‖p_U‖^2 := hxy_sum
      rw [h]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have h_x_cos : x = ‖p_U‖ * Real.cos φ' := by
      have h : ‖p_U‖ * Real.cos φ' = ‖p_U‖ * (x / Real.sqrt (x^2 + y^2)) := by
        rw [hcos_φ']
      rw [h, h_r_eq]
      field_simp [hpU_pos.ne'] <;> ring
    have h_y_sin : y = ‖p_U‖ * Real.sin φ' := by
      have h : ‖p_U‖ * Real.sin φ' = ‖p_U‖ * (y / Real.sqrt (x^2 + y^2)) := by
        rw [hsin_φ']
      rw [h, h_r_eq]
      field_simp [hpU_pos.ne'] <;> ring

    -- inner p_U n = ‖p_U‖ * sin(φ' - α)
    have h_inner_pU_n : inner ℝ p_U n = ‖p_U‖ * Real.sin Δφ := by
      have h1 : inner ℝ p_U n = -Real.sin α * inner ℝ p_U e1 + Real.cos α * inner ℝ p_U e2 := by
        have h_expand : n = -Real.sin α • e1 + Real.cos α • e2 := by rfl
        rw [h_expand]
        rw [inner_add_right, inner_smul_right, inner_smul_right] <;> ring
      rw [h1, hx_eq, hy_eq]
      rw [h_x_cos, h_y_sin]
      have h2 : -Real.sin α * (‖p_U‖ * Real.cos φ') + Real.cos α * (‖p_U‖ * Real.sin φ') =
          ‖p_U‖ * Real.sin (φ' - α) := by
        rw [Real.sin_sub] <;> ring
      exact h2

    -- inner U.direction n = inner p_U n (since n ⟂ T.direction)
    have h_n_perp_T : inner ℝ T.direction n = 0 := by
      have h_expand : n = -Real.sin α • e1 + Real.cos α • e2 := by rfl
      rw [h_expand]
      rw [inner_add_right, inner_smul_right, inner_smul_right, h_perp01, h_perp02] <;> ring
    have h_inner_Un : inner ℝ U.direction n = inner ℝ p_U n := by
      have h3 : U.direction = p_U + c • T.direction := by
        simp [p_U] <;> abel
      rw [h3]
      have h4 : inner ℝ (c • T.direction) n = 0 := by
        rw [inner_smul_left, h_n_perp_T] <;> ring
      rw [inner_add_left, h4] <;> ring

    rw [h_inner_Un, h_inner_pU_n]
    have h_abs : |‖p_U‖ * Real.sin Δφ| = ‖p_U‖ * |Real.sin Δφ| := by
      rw [abs_mul]
      <;> rw [abs_of_nonneg (by positivity)]
    rw [h_abs]
    have h_sin_abs : |Real.sin Δφ| ≤ Δφ := by
      have h : |Real.sin Δφ| ≤ |Δφ| := Real.abs_sin_le_abs
      have h2 : |Δφ| = Δφ := abs_of_nonneg hΔφ_nonneg
      rw [h2] at h
      exact h
    have h_pos1 : 0 ≤ ‖p_U‖ := by positivity
    have h_pos2 : 0 ≤ Δφ := hΔφ_nonneg
    have h_pos3 : 0 ≤ (2 * σ) := by linarith
    have h_dφ : Δφ ≤ bin_width := le_of_lt hΔφ_lt
    have h_mul : ‖p_U‖ * Δφ ≤ (2 * σ) * bin_width :=
      mul_le_mul hpU_le_2σ h_dφ h_pos2 h_pos3
    have h_abs_sin : |Real.sin Δφ| ≤ Δφ := by
      have h : |Real.sin Δφ| ≤ |Δφ| := Real.abs_sin_le_abs
      have h2 : |Δφ| = Δφ := abs_of_nonneg hΔφ_nonneg
      rw [h2] at h
      exact h
    have h_final : ‖p_U‖ * |Real.sin Δφ| ≤ 2 * δ := by
      have h1 : ‖p_U‖ * |Real.sin Δφ| ≤ ‖p_U‖ * Δφ :=
        mul_le_mul_of_nonneg_left h_abs_sin h_pos1
      have h2 : ‖p_U‖ * Δφ ≤ (2 * σ) * bin_width := h_mul
      have h3 : (2 * σ) * bin_width = 2 * δ := by
        dsimp only [bin_width]; field_simp [hσ.ne'] <;> ring
      rw [h3] at h2
      exact le_trans h1 h2
    exact h_final

  have hK_upper : (K : ℝ) ≤ 2 * Real.pi / bin_width + 1 := by
    have h_nonneg : 0 ≤ 2 * Real.pi / bin_width := by positivity
    have h : (K : ℝ) < 2 * Real.pi / bin_width + 1 :=
      Nat.ceil_lt_add_one h_nonneg
    linarith
  have hK_upper' : (K : ℝ) ≤ 2 * Real.pi * σ / δ + 1 := by
    have h_eq : 2 * Real.pi / bin_width = 2 * Real.pi * σ / δ := by
      dsimp only [bin_width]
      field_simp [hδ.ne'] <;> ring
    rw [h_eq] at hK_upper
    exact hK_upper
  exact ⟨K, bins, hK_upper', h_sub, h_cover, h_plane⟩

/-- Distance from x to the infinite line through T.base in direction T.direction. -/
def distToAxis {δ : ℝ} (x : Point3) (T : Kakeya.DeltaTube δ) : ℝ :=
  ‖x - T.base - inner ℝ (x - T.base) T.direction • T.direction‖

/-- 2D determinant in the (e1,e2) plane. -/
def det2 (e1 e2 a b : Point3) : ℝ :=
  inner ℝ a e1 * inner ℝ b e2 - inner ℝ a e2 * inner ℝ b e1

/-- Bessel inequality for two orthonormal vectors. -/
lemma bessel_two (e1 e2 a : Point3)
    (he1 : ‖e1‖ = 1) (he2 : ‖e2‖ = 1) (hperp : inner ℝ e1 e2 = 0) :
    (inner ℝ a e1)^2 + (inner ℝ a e2)^2 ≤ ‖a‖^2 := by
  set x1 := inner ℝ a e1 with hx1
  set x2 := inner ℝ a e2 with hx2
  set b1 := a - x1 • e1 with hb1
  set b2 := b1 - x2 • e2 with hb2
  have h_norm1 : ‖b1‖^2 = ‖a‖^2 - x1^2 := by
    rw [hb1, norm_sub_sq_real]
    have h2 : inner ℝ a (x1 • e1) = x1 * inner ℝ a e1 := by
      simp [inner_smul_right] <;> ring
    have h3 : ‖x1 • e1‖^2 = x1^2 := by
      have h31 : ‖x1 • e1‖ = |x1| := by
        calc ‖x1 • e1‖ = |x1| * ‖e1‖ := norm_smul x1 e1
          _ = |x1| * 1 := by rw [he1]
          _ = |x1| := by ring
      rw [h31]
      exact sq_abs x1
    rw [h2, h3]
    have h4 : x1 * inner ℝ a e1 = x1^2 := by
      rw [←hx1] <;> ring
    rw [h4] <;> ring
  have h_inner_b1_e2 : inner ℝ b1 e2 = x2 := by
    rw [hb1]
    have h : inner ℝ (a - x1 • e1) e2 = inner ℝ a e2 - inner ℝ (x1 • e1) e2 := by
      exact inner_sub_left a (x1 • e1) e2
    rw [h]
    have h2 : inner ℝ (x1 • e1) e2 = x1 * inner ℝ e1 e2 := by
      simp [inner_smul_left] <;> ring
    rw [h2, ←hx2, hperp] <;> ring
  have h_norm2 : ‖b2‖^2 = ‖b1‖^2 - x2^2 := by
    rw [hb2, norm_sub_sq_real]
    have h5 : inner ℝ b1 (x2 • e2) = x2 * inner ℝ b1 e2 := by
      simp [inner_smul_right] <;> ring
    have h7 : ‖x2 • e2‖^2 = x2^2 := by
      have h71 : ‖x2 • e2‖ = |x2| := by
        calc ‖x2 • e2‖ = |x2| * ‖e2‖ := norm_smul x2 e2
          _ = |x2| * 1 := by rw [he2]
          _ = |x2| := by ring
      rw [h71]
      exact sq_abs x2
    rw [h5, h_inner_b1_e2, h7] <;> ring
  have h8 : ‖b2‖^2 = ‖a‖^2 - x1^2 - x2^2 := by
    rw [h_norm2, h_norm1] <;> ring
  have h_nonneg : 0 ≤ ‖b2‖^2 := by positivity
  linarith [h8, h_nonneg]

/-- Cauchy-Schwarz bound for the 2D determinant: |det2| ≤ ‖a‖ * ‖b‖. -/
lemma det2_bound (e1 e2 a b : Point3)
    (he1 : ‖e1‖ = 1) (he2 : ‖e2‖ = 1) (hperp : inner ℝ e1 e2 = 0) :
    |det2 e1 e2 a b| ≤ ‖a‖ * ‖b‖ := by
  let x1 := inner ℝ a e1
  let x2 := inner ℝ a e2
  let y1 := inner ℝ b e1
  let y2 := inner ℝ b e2
  have h_bessel_a : x1^2 + x2^2 ≤ ‖a‖^2 := bessel_two e1 e2 a he1 he2 hperp
  have h_bessel_b : y1^2 + y2^2 ≤ ‖b‖^2 := bessel_two e1 e2 b he1 he2 hperp
  have h_cs : (x1 * y2 - x2 * y1)^2 ≤ (x1^2 + x2^2) * (y1^2 + y2^2) := by
    have h : (x1^2 + x2^2) * (y1^2 + y2^2) - (x1 * y2 - x2 * y1)^2 = (x1 * y1 + x2 * y2)^2 := by ring
    have h' : (x1 * y1 + x2 * y2)^2 ≥ 0 := by positivity
    linarith
  have h5 : (det2 e1 e2 a b)^2 = (x1 * y2 - x2 * y1)^2 := by
    simp [det2, x1, x2, y1, y2] <;> ring
  have h_main : (det2 e1 e2 a b)^2 ≤ (‖a‖ * ‖b‖)^2 := by
    rw [h5]
    calc (x1 * y2 - x2 * y1)^2
      ≤ (x1^2 + x2^2) * (y1^2 + y2^2) := h_cs
    _ ≤ ‖a‖^2 * ‖b‖^2 := by gcongr <;> linarith
    _ = (‖a‖ * ‖b‖)^2 := by ring
  have h6 : 0 ≤ |det2 e1 e2 a b| := by positivity
  have h7 : 0 ≤ ‖a‖ * ‖b‖ := by positivity
  have h10 : (|det2 e1 e2 a b|)^2 = (det2 e1 e2 a b)^2 := by rw [sq_abs]
  have h11 : (|det2 e1 e2 a b|)^2 ≤ (‖a‖ * ‖b‖)^2 := by
    rw [h10]
    exact h_main
  nlinarith

/-- Orthogonal projection onto the perpendicular complement of Tdir. -/
def perpProj (Tdir v : Point3) : Point3 :=
  v - inner ℝ v Tdir • Tdir

lemma perpProj_add (Tdir : Point3) (u v : Point3) :
    perpProj Tdir (u + v) = perpProj Tdir u + perpProj Tdir v := by
  simp [perpProj, inner_add_left, add_smul] <;> abel

lemma perpProj_sub (Tdir : Point3) (u v : Point3) :
    perpProj Tdir (u - v) = perpProj Tdir u - perpProj Tdir v := by
  simp [perpProj, inner_sub_left, sub_smul] <;> abel

lemma perpProj_smul (Tdir : Point3) (c : ℝ) (v : Point3) :
    perpProj Tdir (c • v) = c • perpProj Tdir v := by
  have h : inner ℝ (c • v) Tdir = c * inner ℝ v Tdir :=
    inner_smul_left v Tdir (r := c)
  have h1 : perpProj Tdir (c • v) = c • v - inner ℝ (c • v) Tdir • Tdir := by rfl
  rw [h1, h]
  have h2 : (c * inner ℝ v Tdir) • Tdir = c • (inner ℝ v Tdir • Tdir) := by
    rw [smul_smul] <;> ring
  rw [h2]
  have h3 : perpProj Tdir v = v - inner ℝ v Tdir • Tdir := by rfl
  rw [h3, smul_sub] <;> rfl

lemma perpProj_norm (Tdir : Point3) (hdir : ‖Tdir‖ = 1) (v : Point3) :
    ‖perpProj Tdir v‖ ≤ ‖v‖ := by
  set c := inner ℝ v Tdir with hc
  have h1 : inner ℝ Tdir Tdir = 1 := by
    have h : inner ℝ Tdir Tdir = ‖Tdir‖ ^ 2 := real_inner_self_eq_norm_sq Tdir
    rw [h, hdir] <;> norm_num
  have h_expand : ‖perpProj Tdir v‖ ^ 2 = ‖v‖ ^ 2 - c ^ 2 := by
    have h_eq : perpProj Tdir v = v - c • Tdir := by rfl
    rw [h_eq, norm_sub_sq_real]
    have h2 : inner ℝ v (c • Tdir) = c * inner ℝ v Tdir := inner_smul_right v Tdir (r := c)
    have h3 : ‖c • Tdir‖ ^ 2 = c ^ 2 := by
      have h4 : ‖c • Tdir‖ = |c| * ‖Tdir‖ := norm_smul c Tdir
      have h5 : ‖c • Tdir‖ ^ 2 = (|c| * ‖Tdir‖) ^ 2 := by rw [h4]
      rw [h5]
      have h6 : (|c| * ‖Tdir‖) ^ 2 = |c| ^ 2 * ‖Tdir‖ ^ 2 := by ring
      rw [h6]
      have h7 : |c| ^ 2 = c ^ 2 := sq_abs c
      rw [h7, hdir] <;> ring
    rw [h2, h3, hc] <;> ring
  have h_nonneg : 0 ≤ c ^ 2 := by positivity
  have h4 : ‖perpProj Tdir v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    linarith [h_expand, h_nonneg]
  have h5 : 0 ≤ ‖perpProj Tdir v‖ := by positivity
  have h6 : 0 ≤ ‖v‖ := by positivity
  nlinarith

lemma perpProj_self (Tdir : Point3) (hdir : ‖Tdir‖ = 1) (v : Point3) :
    perpProj Tdir (perpProj Tdir v) = perpProj Tdir v := by
  set c := inner ℝ v Tdir with hc
  have h1 : inner ℝ Tdir Tdir = 1 := by
    have h : inner ℝ Tdir Tdir = ‖Tdir‖ ^ 2 := real_inner_self_eq_norm_sq Tdir
    rw [h, hdir] <;> norm_num
  have h_inner : inner ℝ (perpProj Tdir v) Tdir = 0 := by
    have h_eq : perpProj Tdir v = v - c • Tdir := by rfl
    rw [h_eq]
    have h2 : inner ℝ (v - c • Tdir) Tdir = inner ℝ v Tdir - inner ℝ (c • Tdir) Tdir :=
      inner_sub_left v (c • Tdir) Tdir
    rw [h2]
    have h3 : inner ℝ (c • Tdir) Tdir = c * inner ℝ Tdir Tdir := inner_smul_left Tdir Tdir (r := c)
    rw [h3, h1, hc] <;> ring
  have h4 : perpProj Tdir (perpProj Tdir v) = perpProj Tdir v - inner ℝ (perpProj Tdir v) Tdir • Tdir := by rfl
  rw [h4, h_inner]
  have h5 : (0 : ℝ) • Tdir = 0 := by simp
  rw [h5] <;> abel

lemma perpProj_dir (Tdir : Point3) (hdir : ‖Tdir‖ = 1) :
    perpProj Tdir Tdir = 0 := by
  have h1 : inner ℝ Tdir Tdir = 1 := by
    have h : inner ℝ Tdir Tdir = ‖Tdir‖ ^ 2 := real_inner_self_eq_norm_sq Tdir
    rw [h, hdir] <;> norm_num
  have h2 : perpProj Tdir Tdir = Tdir - inner ℝ Tdir Tdir • Tdir := by rfl
  rw [h2, h1]
  <;> simp

/--
Key angular localization: if U intersects T and x ∈ U.carrier, then the
2D determinant of the perpendicular projections is bounded by 3δ·‖p_U‖.
-/
lemma angular_det_bound
    {δ : ℝ} (hδ : 0 < δ)
    (T U : Kakeya.DeltaTube δ)
    (e1 e2 : Point3)
    (he1 : ‖e1‖ = 1) (he2 : ‖e2‖ = 1)
    (h_perpT1 : inner ℝ T.direction e1 = 0)
    (h_perpT2 : inner ℝ T.direction e2 = 0)
    (h_perp12 : inner ℝ e1 e2 = 0)
    (h_inter : (T.carrier ∩ U.carrier).Nonempty)
    (x : Point3) (hx : x ∈ U.carrier) :
    |det2 e1 e2 (perpProj T.direction U.direction) (perpProj T.direction (x - T.base))| ≤
    3 * δ * ‖perpProj T.direction U.direction‖ := by
  set p_U := perpProj T.direction U.direction with hpU
  set P := perpProj T.direction with hP
  set x_perp := P (x - T.base) with hxperp
  have hP_add := perpProj_add T.direction
  have hP_sub := perpProj_sub T.direction
  have hP_smul := perpProj_smul T.direction
  have hP_norm := perpProj_norm T.direction T.direction_unit
  have hP_self := perpProj_self T.direction T.direction_unit
  have hP_T := perpProj_dir T.direction T.direction_unit
  have hP_pU : P p_U = p_U := hP_self U.direction
  -- Extract witness from x ∈ U.carrier
  have h_compact_seg : ∀ (b d : Point3), IsCompact (unitSegment b d) := by
    intro b d
    have h1 : IsCompact (Set.Icc (0 : ℝ) 1) := isCompact_Icc
    have h2 : Continuous (fun t : ℝ => b + t • d) := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    simpa [unitSegment] using h1.image h2
  have hx' : ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ ‖x - (U.base + t • U.direction)‖ ≤ δ := by
    have h1 : x ∈ Metric.cthickening δ (unitSegment U.base U.direction) := hx
    rw [(h_compact_seg U.base U.direction).cthickening_eq_biUnion_closedBall (by linarith)] at h1
    simp only [Set.mem_iUnion₂] at h1
    rcases h1 with ⟨y, hy, hball⟩
    have hdist : dist x y ≤ δ := (Metric.mem_closedBall).mp hball
    rcases hy with ⟨t, ht, h_eq⟩
    have hdist' : ‖x - (U.base + t • U.direction)‖ ≤ δ := by
      have h : dist x y = ‖x - y‖ := by rfl
      rw [h] at hdist
      rw [h_eq.symm] at hdist
      exact hdist
    exact ⟨t, ht.1, ht.2, hdist'⟩
  rcases hx' with ⟨t, ht0, ht1, hdist_x⟩
  let e_x := x - (U.base + t • U.direction)
  have he_x : ‖e_x‖ ≤ δ := hdist_x
  -- Extract intersection point z
  rcases h_inter with ⟨z, hzT, hzU⟩
  have hzT' : ∃ (sT : ℝ), 0 ≤ sT ∧ sT ≤ 1 ∧ ‖z - (T.base + sT • T.direction)‖ ≤ δ := by
    have h1 : z ∈ Metric.cthickening δ (unitSegment T.base T.direction) := hzT
    rw [(h_compact_seg T.base T.direction).cthickening_eq_biUnion_closedBall (by linarith)] at h1
    simp only [Set.mem_iUnion₂] at h1
    rcases h1 with ⟨y, hy, hball⟩
    have hdist : dist z y ≤ δ := (Metric.mem_closedBall).mp hball
    rcases hy with ⟨s, hs, h_eq⟩
    have hdist' : ‖z - (T.base + s • T.direction)‖ ≤ δ := by
      have h : dist z y = ‖z - y‖ := by rfl
      rw [h] at hdist
      rw [h_eq.symm] at hdist
      exact hdist
    exact ⟨s, hs.1, hs.2, hdist'⟩
  rcases hzT' with ⟨sT, hsT0, hsT1, hdist_zT⟩
  have hzU' : ∃ (sU : ℝ), 0 ≤ sU ∧ sU ≤ 1 ∧ ‖z - (U.base + sU • U.direction)‖ ≤ δ := by
    have h1 : z ∈ Metric.cthickening δ (unitSegment U.base U.direction) := hzU
    rw [(h_compact_seg U.base U.direction).cthickening_eq_biUnion_closedBall (by linarith)] at h1
    simp only [Set.mem_iUnion₂] at h1
    rcases h1 with ⟨y, hy, hball⟩
    have hdist : dist z y ≤ δ := (Metric.mem_closedBall).mp hball
    rcases hy with ⟨s, hs, h_eq⟩
    have hdist' : ‖z - (U.base + s • U.direction)‖ ≤ δ := by
      have h : dist z y = ‖z - y‖ := by rfl
      rw [h] at hdist
      rw [h_eq.symm] at hdist
      exact hdist
    exact ⟨s, hs.1, hs.2, hdist'⟩
  rcases hzU' with ⟨sU, hsU0, hsU1, hdist_zU⟩
  let e_zT := z - (T.base + sT • T.direction)
  let e_zU := z - (U.base + sU • U.direction)
  have he_zT : ‖e_zT‖ ≤ δ := hdist_zT
  have he_zU : ‖e_zU‖ ≤ δ := hdist_zU
  let w := U.base + sU • U.direction
  -- x_perp = P(w - T.base) + (t - sU) • p_U + P(e_x)
  have h_eq1 : x_perp = P (w - T.base) + (t - sU) • p_U + P e_x := by
    have h_x : x = U.base + t • U.direction + e_x := by
      simp [e_x] <;> abel
    have h_sub_smul : (t - sU) • U.direction = t • U.direction - sU • U.direction := by
      rw [sub_smul]
    have h1 : x - T.base = (w - T.base) + (t - sU) • U.direction + e_x := by
      have h_w : w = U.base + sU • U.direction := by rfl
      rw [h_w, h_x, h_sub_smul] <;> abel
    have h2 : P (x - T.base) = P ((w - T.base) + ((t - sU) • U.direction + e_x)) := by
      apply congr_arg P
      rw [h1] <;> abel
    simp only [x_perp]
    rw [h2]
    have h21 : P ((w - T.base) + ((t - sU) • U.direction + e_x)) =
        P (w - T.base) + P ((t - sU) • U.direction + e_x) := hP_add _ _
    rw [h21]
    have h22 : P ((t - sU) • U.direction + e_x) = P ((t - sU) • U.direction) + P e_x := hP_add _ _
    rw [h22]
    have h3 : P ((t - sU) • U.direction) = (t - sU) • P U.direction := hP_smul (t - sU) U.direction
    rw [h3]
    have h4 : P U.direction = p_U := by rfl
    rw [h4] <;> abel
  -- P(w - T.base) = P(e_zT) - P(e_zU)
  have h_eq2 : P (w - T.base) = P e_zT - P e_zU := by
    have hz1 : z = T.base + sT • T.direction + e_zT := by simp [e_zT] <;> abel
    have hz2 : z = w + e_zU := by simp [w, e_zU] <;> abel
    have h3 : w - T.base = e_zT - e_zU + sT • T.direction := by
      calc w - T.base
        = (z - e_zU) - T.base := by rw [hz2] <;> abel
      _ = (T.base + sT • T.direction + e_zT - e_zU) - T.base := by rw [hz1] <;> abel
      _ = e_zT - e_zU + sT • T.direction := by abel
    rw [h3]
    have h4 : P (e_zT - e_zU + sT • T.direction) = P (e_zT - e_zU) + P (sT • T.direction) := hP_add _ _
    rw [h4]
    have h5 : P (e_zT - e_zU) = P e_zT - P e_zU := hP_sub _ _
    rw [h5]
    have h6 : P (sT • T.direction) = sT • P T.direction := hP_smul sT T.direction
    rw [h6]
    have h7 : P T.direction = 0 := by simpa [P] using hP_T
    rw [h7]
    simp
  -- Main determinant computation
  have h_det_add : ∀ (a b c : Point3), det2 e1 e2 p_U (a + b + c) =
      det2 e1 e2 p_U a + det2 e1 e2 p_U b + det2 e1 e2 p_U c := by
    intro a b c
    unfold det2
    have h_i1 : inner ℝ (a + b + c) e2 = inner ℝ a e2 + inner ℝ b e2 + inner ℝ c e2 := by
      rw [inner_add_left, inner_add_left] <;> abel
    have h_i2 : inner ℝ (a + b + c) e1 = inner ℝ a e1 + inner ℝ b e1 + inner ℝ c e1 := by
      rw [inner_add_left, inner_add_left] <;> abel
    rw [h_i1, h_i2] <;> ring
  have h_det_smul : ∀ (c : ℝ) (v : Point3), det2 e1 e2 p_U (c • v) = c * det2 e1 e2 p_U v := by
    intro c v
    unfold det2
    have h_i1 : inner ℝ (c • v) e2 = c * inner ℝ v e2 := inner_smul_left v e2 (r := c)
    have h_i2 : inner ℝ (c • v) e1 = c * inner ℝ v e1 := inner_smul_left v e1 (r := c)
    rw [h_i1, h_i2] <;> ring
  have h8 : det2 e1 e2 p_U ((t - sU) • p_U) = 0 := by
    rw [h_det_smul]
    unfold det2
    have h_self : inner ℝ p_U e1 * inner ℝ p_U e2 - inner ℝ p_U e2 * inner ℝ p_U e1 = 0 := by ring
    rw [h_self] <;> ring
  have h_main : det2 e1 e2 p_U x_perp =
      det2 e1 e2 p_U (P (w - T.base)) + det2 e1 e2 p_U (P e_x) := by
    rw [h_eq1]
    have h7 := h_det_add (P (w - T.base)) ((t - sU) • p_U) (P e_x)
    rw [h7, h8] <;> abel
  have h_final : |det2 e1 e2 p_U x_perp| ≤ 3 * δ * ‖p_U‖ := by
    rw [h_main]
    have h_bound1 : |det2 e1 e2 p_U (P (w - T.base))| ≤ ‖p_U‖ * ‖P (w - T.base)‖ :=
      det2_bound e1 e2 p_U (P (w - T.base)) he1 he2 h_perp12
    have h_bound2 : |det2 e1 e2 p_U (P e_x)| ≤ ‖p_U‖ * ‖P e_x‖ :=
      det2_bound e1 e2 p_U (P e_x) he1 he2 h_perp12
    have h_norm1 : ‖P (w - T.base)‖ ≤ 2 * δ := by
      rw [h_eq2]
      calc ‖P e_zT - P e_zU‖ ≤ ‖P e_zT‖ + ‖P e_zU‖ := norm_sub_le _ _
        _ ≤ ‖e_zT‖ + ‖P e_zU‖ := by gcongr <;> exact hP_norm e_zT
        _ ≤ ‖e_zT‖ + ‖e_zU‖ := by gcongr <;> exact hP_norm e_zU
        _ ≤ δ + δ := by gcongr
        _ = 2 * δ := by ring
    have h_norm2 : ‖P e_x‖ ≤ δ := by
      calc ‖P e_x‖ ≤ ‖e_x‖ := hP_norm e_x
        _ ≤ δ := he_x
    have h_triangle : |det2 e1 e2 p_U (P (w - T.base)) + det2 e1 e2 p_U (P e_x)| ≤
        |det2 e1 e2 p_U (P (w - T.base))| + |det2 e1 e2 p_U (P e_x)| := by
      exact abs_add_le _ _
    calc |det2 e1 e2 p_U (P (w - T.base)) + det2 e1 e2 p_U (P e_x)|
      ≤ |det2 e1 e2 p_U (P (w - T.base))| + |det2 e1 e2 p_U (P e_x)| := h_triangle
    _ ≤ ‖p_U‖ * ‖P (w - T.base)‖ + ‖p_U‖ * ‖P e_x‖ := by gcongr
    _ ≤ ‖p_U‖ * (2 * δ) + ‖p_U‖ * δ := by gcongr
    _ = 3 * δ * ‖p_U‖ := by ring
  simpa [hpU, hxperp, hP] using h_final

/-- Trigonometric helper: if |sin θ| ≤ ε ≤ 1, then θ is within arcsin ε of an integer multiple of π. -/
lemma sin_close_to_int_mul_pi {θ ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h : |Real.sin θ| ≤ ε) :
    ∃ (n : ℤ), |θ - (n : ℝ) * Real.pi| ≤ Real.arcsin ε := by
  let n : ℤ := Int.floor (θ / Real.pi + 1 / 2)
  have h1 : (n : ℝ) ≤ θ / Real.pi + 1 / 2 := Int.floor_le _
  have h2 : θ / Real.pi + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have h41 : θ / Real.pi - (n : ℝ) ≤ 1 / 2 := by linarith
  have h42 : -(1 / 2 : ℝ) ≤ θ / Real.pi - (n : ℝ) := by linarith
  have h4 : |θ / Real.pi - (n : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨h42, h41⟩
  have h51 : θ - (n : ℝ) * Real.pi = (θ / Real.pi - (n : ℝ)) * Real.pi := by
    field_simp [Real.pi_ne_zero] <;> ring
  have h5 : |θ - (n : ℝ) * Real.pi| = |θ / Real.pi - (n : ℝ)| * Real.pi := by
    rw [h51, abs_mul, abs_of_pos Real.pi_pos] <;> ring
  have h3 : |θ - (n : ℝ) * Real.pi| ≤ Real.pi / 2 := by
    rw [h5]
    have h6 : 0 < Real.pi := Real.pi_pos
    nlinarith
  set ψ := θ - (n : ℝ) * Real.pi with hψ
  have hψ_bound : |ψ| ≤ Real.pi / 2 := h3
  have h7 : Real.sin ψ = (-1 : ℝ)^n * Real.sin θ := by
    rw [hψ]
    exact Real.sin_sub_int_mul_pi θ n
  have h71 : |(-1 : ℝ)^n| = 1 := by
    simp [abs_zpow]
    <;> norm_num
  have hsin : |Real.sin ψ| ≤ ε := by
    rw [h7, abs_mul, h71]
    <;> simpa using h
  have h_main : |ψ| ≤ Real.arcsin ε := by
    have h_arcsin_nonneg : 0 ≤ Real.arcsin ε := Real.arcsin_nonneg.mpr hε
    by_cases hψ' : 0 ≤ ψ
    · -- ψ ≥ 0
      have h8 : 0 ≤ ψ := hψ'
      have h9 : ψ ≤ Real.pi / 2 := by linarith [abs_le.mp hψ_bound]
      have h10 : Real.sin ψ ≤ ε := by linarith [abs_le.mp hsin]
      have h11 : ψ ≤ Real.arcsin ε := by
        have h_arcsin_sin : Real.arcsin (Real.sin ψ) = ψ := by
          rw [Real.arcsin_sin] <;> linarith [Real.pi_nonneg]
        have h_sin_nonneg : 0 ≤ Real.sin ψ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
        have h_arcsin_mono : Real.arcsin (Real.sin ψ) ≤ Real.arcsin ε :=
          Real.arcsin_le_arcsin h10
        rw [h_arcsin_sin] at h_arcsin_mono
        exact h_arcsin_mono
      exact abs_le.mpr ⟨by linarith, h11⟩
    · -- ψ < 0
      have h8 : ψ < 0 := by linarith
      have h9 : -Real.pi / 2 ≤ ψ := by linarith [abs_le.mp hψ_bound]
      have h10 : -ε ≤ Real.sin ψ := by linarith [abs_le.mp hsin]
      have h11 : -ψ ≤ Real.arcsin ε := by
        have h12 : Real.sin (-ψ) ≤ ε := by
          have h13 : Real.sin (-ψ) = -Real.sin ψ := by simp
          rw [h13] <;> linarith
        have h14 : 0 ≤ -ψ := by linarith
        have h15 : -ψ ≤ Real.pi / 2 := by linarith
        have h_arcsin_sin : Real.arcsin (Real.sin (-ψ)) = -ψ := by
          rw [Real.arcsin_sin] <;> linarith [Real.pi_nonneg]
        have h_sin_nonneg2 : 0 ≤ Real.sin (-ψ) := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
        have h_arcsin_mono : Real.arcsin (Real.sin (-ψ)) ≤ Real.arcsin ε :=
          Real.arcsin_le_arcsin h12
        rw [h_arcsin_sin] at h_arcsin_mono
        exact h_arcsin_mono
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  exact ⟨n, h_main⟩


end Kakeya.Assouad
