module

/-
  Regular-slope distance bounds for AffineLine.

  Provides Lipschitz and near-point distance bounds using the regular
  slope parameterization y = mx + b (|m| ≤ 1), complementing the existing
  inverse-slope bounds (x = ay + b, |a| ≤ 1) in TubesAndSlopes.lean.

  Key lemmas:
  - regular_slope_lipschitz: |m₁-m₂| ≤ 2·dist_Affine
  - regular_direction_proj_upper_bound: ‖P₁-P₂‖ ≤ 2·|m₁-m₂|

  Whiteprint node: improved_incidence_general / regular_slope_distance
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate

open DiscretisedFurstenbergEstimate
open LemmaE
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Standard basis vector e1 = (1,0). -/
noncomputable def e1 : Plane := EuclideanSpace.single 0 (1 : ℝ)

lemma e1_apply : (e1 : Plane) 0 = 1 ∧ (e1 : Plane) 1 = 0 := by
  simp [e1, EuclideanSpace.single_apply]

lemma e1_norm : ‖(e1 : Plane)‖ = 1 := by
  have h4 := e1_apply
  have h : ‖(e1 : Plane)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [e1, EuclideanSpace.single_apply] <;> ring
  have h5 : 0 ≤ ‖(e1 : Plane)‖ := by positivity
  nlinarith

/-! ### e1 star projection for regular slope -/

/-- Projection of e1 onto line direction with regular slope m = v1/v0.
    For non-vertical lines (v0 ≠ 0): (P e1) = (1/(1+m²), m/(1+m²)). -/
lemma starProjection_e1_semicircle (ℓ : AffineLine)
    (hv0_ne_zero : (getDirV ℓ) 0 ≠ 0) :
    let m := (affineLineSlopeIntercept ℓ).1
    let P := ℓ.1.direction.starProjection
    (P e1) 0 = 1 / (1 + m^2) ∧ (P e1) 1 = m / (1 + m^2) := by
  set v := getDirV ℓ with hv_def
  set m := (affineLineSlopeIntercept ℓ).1 with hm_def
  let P := ℓ.1.direction.starProjection
  have hv_in_dir : v ∈ ℓ.1.direction := (getDirV_spec ℓ).1
  have hv_ne_zero : v ≠ 0 := (getDirV_spec ℓ).2
  have h_m : m = v 1 / v 0 := by
    have h : affineLineSlopeIntercept ℓ =
        (v 1 / v 0, ℓ.offset 1 - (v 1 / v 0) * ℓ.offset 0) := by
      unfold affineLineSlopeIntercept
      dsimp only
      apply Prod.ext
      · split_ifs <;> tauto
      · split_ifs <;> tauto
    rw [hm_def, h] <;> rfl
  have h_dir_eq : ℓ.1.direction = Submodule.span ℝ {v} := by
    have h_span : Submodule.span ℝ {v} ≤ ℓ.1.direction := by
      apply Submodule.span_le.mpr; intro x hx
      have h_x_eq : x = v := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]; exact hv_in_dir
    have h_finrank1 : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 := by
      simp [hv_ne_zero, finrank_span_singleton]
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v}) = Module.finrank ℝ ℓ.1.direction := by
      rw [h_finrank1, ℓ.2]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h2).symm
  have h_inner : inner ℝ e1 v = v 0 := by
    have h_sum : inner ℝ e1 v = ∑ i : Fin 2, inner ℝ (e1 i) (v i) := PiLp.inner_apply e1 v
    rw [h_sum, Fin.sum_univ_two]
    have h4 := e1_apply
    simp [h4.1, h4.2] <;> ring
  have h_norm2 : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
    have h4 : ‖v‖ ^ 2 = inner ℝ v v := by rw [real_inner_self_eq_norm_sq]
    rw [h4]
    have h_sum : inner ℝ v v = ∑ i : Fin 2, inner ℝ (v i) (v i) := PiLp.inner_apply v v
    rw [h_sum, Fin.sum_univ_two]
    have h5 : ∀ (x : ℝ), inner ℝ x x = x * x := by intro x; exact Real.inner_apply x x
    rw [h5 (v 0), h5 (v 1)] <;> ring
  have h_norm_pos : 0 < ‖v‖ ^ 2 := by rw [h_norm2] <;> positivity
  set y : Plane := (inner ℝ e1 v / ‖v‖ ^ 2) • v with hy_def
  have hy_in_K : y ∈ ℓ.1.direction := by
    rw [h_dir_eq]; exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have h_orth : ∀ w ∈ ℓ.1.direction, inner ℝ (e1 - y) w = 0 := by
    intro w hw
    rw [h_dir_eq] at hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    have h4 : inner ℝ (e1 - y) (c • v) = c * inner ℝ (e1 - y) v := by
      rw [inner_smul_right] <;> ring
    rw [h4]
    have h5 : inner ℝ (e1 - y) v = 0 := by
      have h6 : inner ℝ (e1 - y) v = inner ℝ e1 v - inner ℝ y v := by rw [inner_sub_left]
      rw [h6]
      have h7 : inner ℝ y v = (inner ℝ e1 v / ‖v‖ ^ 2) * inner ℝ v v := by
        rw [hy_def, inner_smul_left] <;> simp [real_inner_comm] <;> ring
      rw [h7]
      have h8 : inner ℝ v v = ‖v‖ ^ 2 := by rw [← real_inner_self_eq_norm_sq]
      rw [h8]; field_simp [h_norm_pos.ne'] <;> ring
    rw [h5] <;> ring
  have h_proj_eq : ℓ.1.direction.starProjection e1 = y :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy_in_K h_orth
  have h_main : ℓ.1.direction.starProjection e1 =
      (1 / (1 + m^2)) • (EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 m) := by
    rw [h_proj_eq, hy_def, h_inner, h_norm2, h_m]
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, smul_eq_mul] <;> field_simp [hv0_ne_zero] <;> ring
  dsimp only
  rw [h_main]
  constructor <;> simp [EuclideanSpace.single_apply] <;> field_simp <;> ring

/-! ### Regular slope Lipschitz bound -/

/-- |m₁-m₂| ≤ 2·dist_Affine for lines with |m| ≤ 1. -/
lemma regular_slope_lipschitz (ℓ₁ ℓ₂ : AffineLine)
    (h1_v0 : (getDirV ℓ₁) 0 ≠ 0)
    (h2_v0 : (getDirV ℓ₂) 0 ≠ 0)
    (h1_slope : |(affineLineSlopeIntercept ℓ₁).1| ≤ 1)
    (h2_slope : |(affineLineSlopeIntercept ℓ₂).1| ≤ 1) :
    |(affineLineSlopeIntercept ℓ₁).1 - (affineLineSlopeIntercept ℓ₂).1| ≤
    2 * AffineLine.dist ℓ₁ ℓ₂ := by
  set m1 := (affineLineSlopeIntercept ℓ₁).1 with hm1
  set m2 := (affineLineSlopeIntercept ℓ₂).1 with hm2
  let P1 := ℓ₁.1.direction.starProjection
  let P2 := ℓ₂.1.direction.starProjection
  have hP1 := starProjection_e1_semicircle ℓ₁ h1_v0
  have hP2 := starProjection_e1_semicircle ℓ₂ h2_v0
  have h_denom_le : (1 + m1^2) * (1 + m2^2) ≤ 4 := by
    have h1 : m1^2 ≤ 1 := by nlinarith [abs_le.mp h1_slope]
    have h2 : m2^2 ≤ 1 := by nlinarith [abs_le.mp h2_slope]
    nlinarith
  have h_denom_pos : 0 < (1 + m1^2) * (1 + m2^2) := by positivity
  have h_norm2 : ‖(P1 - P2) e1‖ ^ 2 =
      (m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2)) := by
    have h_sub : (P1 - P2) e1 = P1 e1 - P2 e1 := by rfl
    have h_image0 : ((P1 - P2) e1) 0 = 1 / (1 + m1^2) - 1 / (1 + m2^2) := by
      rw [h_sub]; have h : (P1 e1 - P2 e1) 0 = (P1 e1) 0 - (P2 e1) 0 := by simp
      rw [h, hP1.1, hP2.1] <;> rfl
    have h_image1 : ((P1 - P2) e1) 1 = m1 / (1 + m1^2) - m2 / (1 + m2^2) := by
      rw [h_sub]; have h : (P1 e1 - P2 e1) 1 = (P1 e1) 1 - (P2 e1) 1 := by simp
      rw [h, hP1.2, hP2.2] <;> rfl
    rw [EuclideanSpace.real_norm_sq_eq ((P1 - P2) e1), Fin.sum_univ_two, h_image0, h_image1]
    have h_comm : (1 / (1 + m1^2) - 1 / (1 + m2^2))^2 + (m1 / (1 + m1^2) - m2 / (1 + m2^2))^2 =
        (m1 / (1 + m1^2) - m2 / (1 + m2^2))^2 + (1 / (1 + m1^2) - 1 / (1 + m2^2))^2 := by ring
    rw [h_comm]
    exact TubesAndSlopes.semicircle_chord_algebraic m1 m2
  have h4 : ‖(P1 - P2) e1‖ ^ 2 ≥ (m1 - m2)^2 / 4 := by
    rw [h_norm2]
    have h5 : (m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2)) ≥ (m1 - m2)^2 / 4 := by
      gcongr <;> nlinarith
    exact h5
  have h6 : ‖(P1 - P2) e1‖ ≥ |m1 - m2| / 2 := by
    have h7 : 0 ≤ ‖(P1 - P2) e1‖ := by positivity
    have h8 : |m1 - m2| / 2 ≥ 0 := by positivity
    nlinarith [sq_abs (m1 - m2)]
  have h9 : ‖(P1 - P2) e1‖ ≤ ‖P1 - P2‖ := by
    have h10 : ‖(P1 - P2) e1‖ ≤ ‖P1 - P2‖ * ‖e1‖ := ContinuousLinearMap.le_opNorm (P1 - P2) e1
    rw [e1_norm] at h10 <;> linarith
  have h10 : ‖P1 - P2‖ ≤ AffineLine.dist ℓ₁ ℓ₂ := by
    have h11 : AffineLine.dist ℓ₁ ℓ₂ = ‖P1 - P2‖ + ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    rw [h11]; exact le_add_of_nonneg_right (by positivity)
  linarith

/-! ### Regular slope direction projection upper bound -/

/-- Unit direction vector for regular slope m: (1,m)/√(1+m²). -/
noncomputable def regularSlopeUnitVec (m : ℝ) : Plane :=
  (1 / Real.sqrt (1 + m^2)) • (EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 m)

lemma regularSlopeUnitVec_norm (m : ℝ) : ‖regularSlopeUnitVec m‖ = 1 := by
  have h_pos : 0 < 1 + m^2 := by nlinarith
  have h_sqrt_pos : 0 < Real.sqrt (1 + m^2) := Real.sqrt_pos.mpr h_pos
  let w : Plane := EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 m
  have hw_norm2 : ‖w‖ ^ 2 = 1 + m^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [w, EuclideanSpace.single_apply] <;> ring
  have h1 : ‖regularSlopeUnitVec m‖ = |(1 / Real.sqrt (1 + m^2))| * ‖w‖ := norm_smul _ _
  have h2 : |(1 / Real.sqrt (1 + m^2))| = 1 / Real.sqrt (1 + m^2) := by
    apply abs_of_pos; positivity
  rw [h1, h2]
  have h3 : ‖w‖ = Real.sqrt (1 + m^2) := by
    have h4 : 0 ≤ ‖w‖ := by positivity
    nlinarith [hw_norm2, Real.sq_sqrt (show 0 ≤ 1 + m^2 by nlinarith)]
  rw [h3]; field_simp [h_sqrt_pos.ne'] <;> ring

lemma regularSlopeUnitVec_dist (m1 m2 : ℝ) :
    ‖regularSlopeUnitVec m1 - regularSlopeUnitVec m2‖ ≤ |m1 - m2| := by
  set u1 := regularSlopeUnitVec m1 with hu1
  set u2 := regularSlopeUnitVec m2 with hu2
  set s1 := Real.sqrt (1 + m1^2) with hs1
  set s2 := Real.sqrt (1 + m2^2) with hs2
  set D := s1 * s2 with hD
  have hs1_pos : 0 < s1 := by positivity
  have hs2_pos : 0 < s2 := by positivity
  have hD_pos : 0 < D := mul_pos hs1_pos hs2_pos
  have hD2 : D^2 = (1 + m1^2) * (1 + m2^2) := by
    simp only [hD, hs1, hs2]
    have h : (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2))^2 = (1 + m1^2) * (1 + m2^2) := by
      rw [mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)] <;> ring
    exact h
  have hD_ge1 : D ≥ 1 := by
    have h : D^2 ≥ 1 := by rw [hD2]; nlinarith
    nlinarith [hD_pos]
  have h_abs_sq : D^2 - (|m1 * m2| + 1)^2 = (|m1| - |m2|)^2 := by
    have h1 : |m1 * m2| = |m1| * |m2| := by rw [abs_mul]
    have h2 : D^2 - (|m1| * |m2| + 1)^2 = (|m1| - |m2|)^2 := by
      rw [hD2]
      have h3 : |m1| ^ 2 = m1 ^ 2 := by simp [sq_abs]
      have h4 : |m2| ^ 2 = m2 ^ 2 := by simp [sq_abs]
      nlinarith [sq_nonneg (|m1| - |m2|)]
    simpa [h1] using h2
  have h_D_ge_abs : D ≥ |m1 * m2| + 1 := by
    have h4 : D^2 - (|m1 * m2| + 1)^2 ≥ 0 := by
      rw [h_abs_sq]; exact sq_nonneg _
    have h5 : 0 ≤ D := by positivity
    have h6 : 0 ≤ |m1 * m2| + 1 := by positivity
    nlinarith
  have h_sum_ge2 : D + m1 * m2 + 1 ≥ 2 := by
    have h7 : |m1 * m2| + m1 * m2 ≥ 0 := by
      cases' abs_cases (m1 * m2) with h8 h8 <;> linarith
    linarith [h_D_ge_abs]
  have h_denom_ge2 : D * (D + m1 * m2 + 1) ≥ 2 := by
    have h9 : D ≥ 1 := hD_ge1
    nlinarith
  have h_sum_pos : 0 < D + m1 * m2 + 1 := by linarith [h_sum_ge2]
  have h_u1_norm : ‖u1‖ = 1 := regularSlopeUnitVec_norm m1
  have h_u2_norm : ‖u2‖ = 1 := regularSlopeUnitVec_norm m2
  set w1 : Plane := EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 m1 with hw1
  set w2 : Plane := EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 m2 with hw2
  have h_u1_eq : u1 = (1 / s1) • w1 := by
    have h : regularSlopeUnitVec m1 = (1 / s1) • w1 := by
      simp [regularSlopeUnitVec, hs1, hw1] <;> rfl
    exact hu1 ▸ h
  have h_u2_eq : u2 = (1 / s2) • w2 := by
    have h : regularSlopeUnitVec m2 = (1 / s2) • w2 := by
      simp [regularSlopeUnitVec, hs2, hw2] <;> rfl
    exact hu2 ▸ h
  have h_inner_w : inner ℝ w1 w2 = 1 + m1 * m2 := by
    have h_sum : inner ℝ w1 w2 = ∑ i : Fin 2, inner ℝ (w1 i) (w2 i) := PiLp.inner_apply w1 w2
    rw [h_sum, Fin.sum_univ_two]
    simp [hw1, hw2, EuclideanSpace.single_apply] <;> ring
  have h_inner : inner ℝ u1 u2 = (1 + m1 * m2) / D := by
    rw [h_u1_eq, h_u2_eq]
    have h1 : inner ℝ ((1 / s1) • w1) ((1 / s2) • w2) = (1 / s1) * (1 / s2) * inner ℝ w1 w2 := by
      have h_a : inner ℝ ((1 / s1) • w1) ((1 / s2) • w2) = (1 / s1) * inner ℝ w1 ((1 / s2) • w2) := by
        simpa [inner_smul_left] using rfl
      rw [h_a]
      have h_b : inner ℝ w1 ((1 / s2) • w2) = (1 / s2) * inner ℝ w1 w2 := by
        simpa [inner_smul_right] using rfl
      rw [h_b] <;> ring
    rw [h1, h_inner_w]
    field_simp [hD, hs1, hs2, hs1_pos.ne', hs2_pos.ne'] <;> ring
  have h_norm2 : ‖u1 - u2‖ ^ 2 = 2 - 2 * inner ℝ u1 u2 := by
    have h_id : ‖u1 - u2‖ ^ 2 = ‖u1‖ ^ 2 + ‖u2‖ ^ 2 - 2 * inner ℝ u1 u2 := by
      have h_norm_sq : ∀ (v : Plane), ‖v‖ ^ 2 = inner ℝ v v := by
        intro v; rw [← real_inner_self_eq_norm_sq]
      rw [h_norm_sq (u1 - u2)]
      have h : inner ℝ (u1 - u2) (u1 - u2) = inner ℝ u1 u1 - inner ℝ u1 u2 - inner ℝ u2 u1 + inner ℝ u2 u2 := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right] <;> ring
      rw [h]
      have h_comm : inner ℝ u2 u1 = inner ℝ u1 u2 := by exact real_inner_comm u1 u2
      rw [h_comm]
      have h1 : inner ℝ u1 u1 = ‖u1‖ ^ 2 := by rw [← real_inner_self_eq_norm_sq]
      have h2 : inner ℝ u2 u2 = ‖u2‖ ^ 2 := by rw [← real_inner_self_eq_norm_sq]
      rw [h1, h2] <;> ring
    rw [h_id, h_u1_norm, h_u2_norm] <;> ring
  have h_id1 : D^2 - (1 + m1 * m2)^2 = (m1 - m2)^2 := by
    rw [hD2] <;> ring
  have h_sum_pos2 : 0 < D + 1 + m1 * m2 := by linarith [h_sum_pos]
  have h6 : (D - (1 + m1 * m2)) * (D + 1 + m1 * m2) = (m1 - m2)^2 := by
    linarith [h_id1]
  have h5 : D - (1 + m1 * m2) = (m1 - m2)^2 / (D + 1 + m1 * m2) := by
    exact (eq_div_iff h_sum_pos2.ne').mpr h6
  have h_final : ‖u1 - u2‖ ^ 2 = 2 * (m1 - m2)^2 / (D * (D + 1 + m1 * m2)) := by
    rw [h_norm2, h_inner]
    have h7 : 2 - 2 * ((1 + m1 * m2) / D) = 2 * (D - (1 + m1 * m2)) / D := by
      field_simp [hD_pos.ne'] <;> ring
    rw [h7]
    have h8 : 2 * (D - (1 + m1 * m2)) / D = 2 * (m1 - m2)^2 / (D * (D + 1 + m1 * m2)) := by
      rw [h5]
      field_simp [hD_pos.ne', h_sum_pos.ne'] <;> ring
    exact h8
  have h6 : ‖u1 - u2‖ ^ 2 ≤ (m1 - m2)^2 := by
    rw [h_final]
    have h7 : 0 ≤ (m1 - m2)^2 := by positivity
    have h8 : 0 < D * (D + 1 + m1 * m2) := mul_pos hD_pos h_sum_pos2
    have h9 : 2 ≤ D * (D + 1 + m1 * m2) := by
      have h10 : D + 1 + m1 * m2 = D + m1 * m2 + 1 := by ring
      rw [h10]
      exact h_denom_ge2
    have h10 : 2 * (m1 - m2)^2 / (D * (D + 1 + m1 * m2)) ≤ (m1 - m2)^2 := by
      calc 2 * (m1 - m2)^2 / (D * (D + 1 + m1 * m2))
          = (2 / (D * (D + 1 + m1 * m2))) * (m1 - m2)^2 := by ring
      _ ≤ 1 * (m1 - m2)^2 := by
        gcongr
        have h11 : 2 / (D * (D + 1 + m1 * m2)) ≤ 1 := by
          apply (div_le_one (by positivity)).mpr
          exact h9
        exact h11
      _ = (m1 - m2)^2 := by ring
    exact h10
  have h11 : (m1 - m2)^2 = |m1 - m2|^2 := by rw [sq_abs]
  rw [h11] at h6
  have h12 : 0 ≤ ‖u1 - u2‖ := by positivity
  have h13 : 0 ≤ |m1 - m2| := by positivity
  have h14 : |‖u1 - u2‖| = ‖u1 - u2‖ := by rw [abs_of_nonneg h12]
  have h15 : |(|m1 - m2|)| = |m1 - m2| := by rw [abs_of_nonneg h13]
  have h16 : |‖u1 - u2‖| ≤ |(|m1 - m2|)| := sq_le_sq.mp h6
  rw [h14, h15] at h16
  exact h16

/-- ‖P₁-P₂‖ ≤ 2·|m₁-m₂| for regular slopes. -/
lemma regular_direction_proj_upper_bound (ℓ₁ ℓ₂ : AffineLine)
    (h1_v0 : (getDirV ℓ₁) 0 ≠ 0)
    (h2_v0 : (getDirV ℓ₂) 0 ≠ 0) :
    ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤
    2 * |(affineLineSlopeIntercept ℓ₁).1 - (affineLineSlopeIntercept ℓ₂).1| := by
  set m1 := (affineLineSlopeIntercept ℓ₁).1 with hm1
  set m2 := (affineLineSlopeIntercept ℓ₂).1 with hm2
  set v1 := getDirV ℓ₁ with hv1_def
  set v2 := getDirV ℓ₂ with hv2_def
  have h_m1 : m1 = v1 1 / v1 0 := by
    have h : affineLineSlopeIntercept ℓ₁ =
        (v1 1 / v1 0, ℓ₁.offset 1 - (v1 1 / v1 0) * ℓ₁.offset 0) := by
      unfold affineLineSlopeIntercept
      dsimp only
      apply Prod.ext
      · split_ifs <;> tauto
      · split_ifs <;> tauto
    rw [hm1, h] <;> rfl
  have h_m2 : m2 = v2 1 / v2 0 := by
    have h : affineLineSlopeIntercept ℓ₂ =
        (v2 1 / v2 0, ℓ₂.offset 1 - (v2 1 / v2 0) * ℓ₂.offset 0) := by
      unfold affineLineSlopeIntercept
      dsimp only
      apply Prod.ext
      · split_ifs <;> tauto
      · split_ifs <;> tauto
    rw [hm2, h] <;> rfl
  have h_dir1_eq : ℓ₁.1.direction = Submodule.span ℝ {v1} := by
    have h_span : Submodule.span ℝ {v1} ≤ ℓ₁.1.direction := by
      apply Submodule.span_le.mpr; intro x hx
      have h_x_eq : x = v1 := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]; exact (getDirV_spec ℓ₁).1
    have h_ne : v1 ≠ 0 := (getDirV_spec ℓ₁).2
    have h_finrank1 : Module.finrank ℝ (Submodule.span ℝ {v1}) = 1 := finrank_span_singleton h_ne
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v1}) = Module.finrank ℝ ℓ₁.1.direction := by
      rw [h_finrank1, ℓ₁.2]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h2).symm
  have h_dir2_eq : ℓ₂.1.direction = Submodule.span ℝ {v2} := by
    have h_span : Submodule.span ℝ {v2} ≤ ℓ₂.1.direction := by
      apply Submodule.span_le.mpr; intro x hx
      have h_x_eq : x = v2 := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]; exact (getDirV_spec ℓ₂).1
    have h_ne : v2 ≠ 0 := (getDirV_spec ℓ₂).2
    have h_finrank2 : Module.finrank ℝ (Submodule.span ℝ {v2}) = 1 := finrank_span_singleton h_ne
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v2}) = Module.finrank ℝ ℓ₂.1.direction := by
      rw [h_finrank2, ℓ₂.2]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h2).symm
  let u1 := regularSlopeUnitVec m1
  let u2 := regularSlopeUnitVec m2
  let s1 := Real.sqrt (1 + m1^2)
  let s2 := Real.sqrt (1 + m2^2)
  have hs1_pos : 0 < s1 := by positivity
  have hs2_pos : 0 < s2 := by positivity
  have h_v1_eq : v1 1 = m1 * v1 0 := by
    rw [h_m1] <;> field_simp [h1_v0] <;> ring
  have h_v2_eq : v2 1 = m2 * v2 0 := by
    rw [h_m2] <;> field_simp [h2_v0] <;> ring
  have h_v1_0 : ((v1 0 * s1) • u1) 0 = v1 0 := by
    simp [u1, regularSlopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul]
    <;> field_simp [hs1_pos.ne'] <;> ring
  have h_v1_1 : ((v1 0 * s1) • u1) 1 = v1 1 := by
    simp [u1, regularSlopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul, h_v1_eq]
    <;> field_simp [hs1_pos.ne'] <;> ring
  have h_v1_scalar : v1 = (v1 0 * s1) • u1 := by
    ext i
    fin_cases i
    · exact h_v1_0.symm
    · exact h_v1_1.symm
  have h_v2_0 : ((v2 0 * s2) • u2) 0 = v2 0 := by
    simp [u2, regularSlopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul]
    <;> field_simp [hs2_pos.ne'] <;> ring
  have h_v2_1 : ((v2 0 * s2) • u2) 1 = v2 1 := by
    simp [u2, regularSlopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul, h_v2_eq]
    <;> field_simp [hs2_pos.ne'] <;> ring
  have h_v2_scalar : v2 = (v2 0 * s2) • u2 := by
    ext i
    fin_cases i
    · exact h_v2_0.symm
    · exact h_v2_1.symm
  let c1 := v1 0 * s1
  let c2 := v2 0 * s2
  have h_c1_ne_zero : c1 ≠ 0 := by
    simp [c1, h1_v0, hs1_pos.ne'] <;> exact h1_v0
  have h_c2_ne_zero : c2 ≠ 0 := by
    simp [c2, h2_v0, hs2_pos.ne'] <;> exact h2_v0
  have h_isUnit1 : IsUnit c1 := IsUnit.mk0 c1 h_c1_ne_zero
  have h_isUnit2 : IsUnit c2 := IsUnit.mk0 c2 h_c2_ne_zero
  have h_span1 : Submodule.span ℝ {v1} = Submodule.span ℝ {u1} := by
    rw [h_v1_scalar]; exact Submodule.span_singleton_smul_eq h_isUnit1 u1
  have h_span2 : Submodule.span ℝ {v2} = Submodule.span ℝ {u2} := by
    rw [h_v2_scalar]; exact Submodule.span_singleton_smul_eq h_isUnit2 u2
  let P1 := Submodule.starProjection (Submodule.span ℝ {u1})
  let P2 := Submodule.starProjection (Submodule.span ℝ {u2})
  have h_proj1_eq : ℓ₁.1.direction.starProjection = P1 := by
    rw [h_dir1_eq, h_span1]
  have h_proj2_eq : ℓ₂.1.direction.starProjection = P2 := by
    rw [h_dir2_eq, h_span2]
  rw [h_proj1_eq, h_proj2_eq]
  have h_u1_norm : ‖u1‖ = 1 := regularSlopeUnitVec_norm m1
  have h_u2_norm : ‖u2‖ = 1 := regularSlopeUnitVec_norm m2
  have h_bound : ∀ (x : Plane), ‖(P1 - P2) x‖ ≤ 2 * ‖u1 - u2‖ * ‖x‖ := by
    intro x
    have h1 : P1 x = inner ℝ u1 x • u1 :=
      Submodule.starProjection_unit_singleton ℝ h_u1_norm x
    have h2 : P2 x = inner ℝ u2 x • u2 :=
      Submodule.starProjection_unit_singleton ℝ h_u2_norm x
    have h3 : (P1 - P2) x = P1 x - P2 x := by
      exact ContinuousLinearMap.sub_apply P1 P2 x
    rw [h3, h1, h2]
    have h4 : inner ℝ u1 x • u1 - inner ℝ u2 x • u2 =
        inner ℝ x (u1 - u2) • u1 + inner ℝ u2 x • (u1 - u2) := by
      have h5 : inner ℝ u1 x = inner ℝ x (u1 - u2) + inner ℝ u2 x := by
        have h_comm1 : inner ℝ u1 x = inner ℝ x u1 := by exact real_inner_comm x u1
        have h_comm2 : inner ℝ u2 x = inner ℝ x u2 := by exact real_inner_comm x u2
        have h_sum : inner ℝ x (u1 - u2) + inner ℝ x u2 = inner ℝ x ((u1 - u2) + u2) := by
          have h : ∀ (a b : Plane), inner ℝ x a + inner ℝ x b = inner ℝ x (a + b) := by
            intro a b
            have h' : inner ℝ x (a + b) = inner ℝ x a + inner ℝ x b := by
              rw [PiLp.inner_apply x (a + b), PiLp.inner_apply x a, PiLp.inner_apply x b]
              have h_term : ∀ i : Fin 2, inner ℝ (x i) ((a + b) i) = inner ℝ (x i) (a i) + inner ℝ (x i) (b i) := by
                intro i
                simp [mul_add] <;> ring
              rw [Finset.sum_congr rfl (fun i _ => h_term i), Finset.sum_add_distrib]
            exact h'.symm
          exact h (u1 - u2) u2
        have h6 : (u1 - u2) + u2 = u1 := by abel
        calc inner ℝ u1 x
          = inner ℝ x u1 := h_comm1
        _ = inner ℝ x ((u1 - u2) + u2) := by rw [h6]
        _ = inner ℝ x (u1 - u2) + inner ℝ x u2 := h_sum.symm
        _ = inner ℝ x (u1 - u2) + inner ℝ u2 x := by rw [h_comm2]
      rw [h5]
      rw [add_smul, smul_sub]
      <;> abel
    rw [h4]
    have h_cs1 : |inner ℝ x (u1 - u2)| ≤ ‖x‖ * ‖u1 - u2‖ := abs_real_inner_le_norm x (u1 - u2)
    have h_cs2 : |inner ℝ u2 x| ≤ ‖u2‖ * ‖x‖ := abs_real_inner_le_norm u2 x
    calc ‖inner ℝ x (u1 - u2) • u1 + inner ℝ u2 x • (u1 - u2)‖
      ≤ ‖inner ℝ x (u1 - u2) • u1‖ + ‖inner ℝ u2 x • (u1 - u2)‖ := norm_add_le _ _
    _ = |inner ℝ x (u1 - u2)| * ‖u1‖ + |inner ℝ u2 x| * ‖u1 - u2‖ := by
      have h_n1 : ‖inner ℝ x (u1 - u2)‖ = |inner ℝ x (u1 - u2)| := by exact Real.norm_eq_abs (inner ℝ x (u1 - u2))
      have h_n2 : ‖inner ℝ u2 x‖ = |inner ℝ u2 x| := by exact Real.norm_eq_abs (inner ℝ u2 x)
      rw [norm_smul, norm_smul, h_n1, h_n2] <;> ring
    _ ≤ (‖x‖ * ‖u1 - u2‖) * ‖u1‖ + (‖u2‖ * ‖x‖) * ‖u1 - u2‖ := by
      gcongr
    _ = ‖x‖ * ‖u1 - u2‖ * 1 + 1 * ‖x‖ * ‖u1 - u2‖ := by
      rw [h_u1_norm, h_u2_norm] <;> ring
    _ = 2 * ‖u1 - u2‖ * ‖x‖ := by ring
  have h_op_norm : ‖P1 - P2‖ ≤ 2 * ‖u1 - u2‖ :=
    ContinuousLinearMap.opNorm_le_bound (P1 - P2) (by positivity) h_bound
  have h_dist : ‖u1 - u2‖ ≤ |m1 - m2| := regularSlopeUnitVec_dist m1 m2
  linarith

end DirecretisedFurstenbergEstimate

end
