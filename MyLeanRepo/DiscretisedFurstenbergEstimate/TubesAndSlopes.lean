module

/-
  Tubes and slopes converse: S-set property transfers from tube family to slope set.

  ## Main result
  - `tubesAndSlopes_converse`: slope set inherits S-set property

  Whiteprint node: tubes_and_slopes_converse
  Dependencies: MainAppendixLemmaE, CoveringUtils
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate
open LemmaE
open DiscretisedFurstenbergEstimate.CoveringUtils

namespace TubesAndSlopes

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def e2 : Plane := EuclideanSpace.single 1 (1 : ℝ)

lemma e2_apply : (e2 : Plane) 0 = 0 ∧ (e2 : Plane) 1 = 1 := by
  constructor <;> simp [e2, EuclideanSpace.single_apply] <;> decide

lemma e2_norm : ‖(e2 : Plane)‖ = 1 := by
  have h4 := e2_apply
  have h5 : ‖(e2 : Plane)‖ ^ 2 = 1 := by
    have h6 : ‖(e2 : Plane)‖ ^ 2 = (e2 : Plane) 0 ^ 2 + (e2 : Plane) 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    rw [h6, h4.1, h4.2] <;> norm_num
  have h7 : 0 ≤ ‖(e2 : Plane)‖ := by positivity
  nlinarith

/-- Algebraic identity: chord length on projection semicircle. -/
lemma semicircle_chord_algebraic (a1 a2 : ℝ) :
    (a1 / (1 + a1^2) - a2 / (1 + a2^2))^2 +
    (1 / (1 + a1^2) - 1 / (1 + a2^2))^2 =
    (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) := by
  have h1 : a1 / (1 + a1^2) - a2 / (1 + a2^2) =
      (a1 - a2) * (1 - a1 * a2) / ((1 + a1^2) * (1 + a2^2)) := by
    field_simp <;> ring
  have h2 : (1 : ℝ) / (1 + a1^2) - (1 : ℝ) / (1 + a2^2) =
      -(a1 - a2) * (a1 + a2) / ((1 + a1^2) * (1 + a2^2)) := by
    field_simp <;> ring
  rw [h1, h2]
  have h3 : (1 - a1 * a2)^2 + (a1 + a2)^2 = (1 + a1^2) * (1 + a2^2) := by ring
  field_simp
  <;> rw [h3] <;> ring

/-- Star projection of line direction onto e2 gives semicircle point. -/
lemma starProjection_e2_semicircle (ℓ : AffineLine)
    (hv1_ne_zero : (getDirV ℓ) 1 ≠ 0) :
    let a := (affineLineParams ℓ).1
    let P := ℓ.1.direction.starProjection
    (P e2) 0 = a / (1 + a^2) ∧ (P e2) 1 = 1 / (1 + a^2) := by
  set v := getDirV ℓ with hv_def
  set a := (affineLineParams ℓ).1 with ha_def
  let P := ℓ.1.direction.starProjection
  have hv_in_dir : v ∈ ℓ.1.direction := (getDirV_spec ℓ).1
  have hv_ne_zero : v ≠ 0 := (getDirV_spec ℓ).2
  have h_a1 : (affineLineParams ℓ).1 = v 0 / v 1 := by
    have h : affineLineParams ℓ =
        (if v 1 = 0 then (0 : ℝ) else v 0 / v 1,
         ℓ.offset 0 - (if v 1 = 0 then (0 : ℝ) else v 0 / v 1) * ℓ.offset 1) := by
      simp [affineLineParams, hv_def] <;> rfl
    rw [h]
    simp [hv1_ne_zero] <;> aesop
  have h_a : a = v 0 / v 1 := by rw [ha_def, h_a1]
  have h_span : Submodule.span ℝ {v} ≤ ℓ.1.direction := by
    apply Submodule.span_le.mpr
    intro x hx
    have h_x_eq : x = v := by simpa [Set.mem_singleton_iff] using hx
    rw [h_x_eq]; exact hv_in_dir
  have h_finrank1 : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 := by
    simp [hv_ne_zero, finrank_span_singleton]
  have h_dir_eq : ℓ.1.direction = Submodule.span ℝ {v} := by
    have h1 : Module.finrank ℝ ℓ.1.direction = 1 := ℓ.2
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v}) = Module.finrank ℝ ℓ.1.direction := by
      rw [h_finrank1, h1]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h2).symm
  have h2 : inner ℝ e2 v = v 1 := by
    have h_sum : inner ℝ e2 v = ∑ i : Fin 2, inner ℝ (e2 i) (v i) := PiLp.inner_apply e2 v
    rw [h_sum, Fin.sum_univ_two]
    have h4 := e2_apply
    simp [h4.1, h4.2] <;> ring
  have h3 : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
    have h4 : ‖v‖ ^ 2 = inner ℝ v v := by rw [real_inner_self_eq_norm_sq]
    rw [h4]
    have h_sum : inner ℝ v v = ∑ i : Fin 2, inner ℝ (v i) (v i) := PiLp.inner_apply v v
    rw [h_sum, Fin.sum_univ_two]
    have h5 : ∀ (x : ℝ), inner ℝ x x = x * x := by intro x; exact Real.inner_apply x x
    rw [h5 (v 0), h5 (v 1)] <;> ring
  have h_norm_pos : 0 < ‖v‖ ^ 2 := by rw [h3] <;> positivity
  set y : Plane := (inner ℝ e2 v / ‖v‖ ^ 2) • v with hy_def
  have hy_in_K : y ∈ ℓ.1.direction := by
    rw [h_dir_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have h_orth : ∀ w ∈ ℓ.1.direction, inner ℝ (e2 - y) w = 0 := by
    intro w hw
    rw [h_dir_eq] at hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    have h4 : inner ℝ (e2 - y) (c • v) = c * inner ℝ (e2 - y) v := by
      rw [inner_smul_right] <;> ring
    rw [h4]
    have h5 : inner ℝ (e2 - y) v = 0 := by
      have h6 : inner ℝ (e2 - y) v = inner ℝ e2 v - inner ℝ y v := by rw [inner_sub_left]
      rw [h6]
      have h7 : inner ℝ y v = (inner ℝ e2 v / ‖v‖ ^ 2) * inner ℝ v v := by
        rw [hy_def, inner_smul_left] <;> simp [real_inner_comm] <;> ring
      rw [h7]
      have h8 : inner ℝ v v = ‖v‖ ^ 2 := by rw [← real_inner_self_eq_norm_sq]
      rw [h8]
      field_simp [h_norm_pos.ne'] <;> ring
    rw [h5] <;> ring
  have h_proj_eq : ℓ.1.direction.starProjection e2 = y :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hy_in_K h_orth
  have h_main : ℓ.1.direction.starProjection e2 =
      (1 / (1 + a^2)) • (EuclideanSpace.single 0 a + EuclideanSpace.single 1 (1 : ℝ)) := by
    rw [h_proj_eq, hy_def, h2, h3, h_a]
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, smul_eq_mul] <;> field_simp [hv1_ne_zero] <;> ring
  dsimp only
  rw [h_main]
  constructor <;> simp [EuclideanSpace.single_apply] <;> field_simp <;> ring

/-- Explicit formula for the offset (orthogonal projection of 0 onto line).
    For line x = a*y + b, offset = (b/(1+a²), -ab/(1+a²)). -/
lemma offset_formula (ℓ : AffineLine) (hv1 : (getDirV ℓ) 1 ≠ 0) :
    ℓ.offset 0 = (affineLineParams ℓ).2 / (1 + (affineLineParams ℓ).1^2) ∧
    ℓ.offset 1 = - (affineLineParams ℓ).1 * (affineLineParams ℓ).2 / (1 + (affineLineParams ℓ).1^2) := by
  set a := (affineLineParams ℓ).1 with ha_def
  set b := (affineLineParams ℓ).2 with hb_def
  set v := getDirV ℓ with hv_def
  have h_a : a = v 0 / v 1 := by
    have h : (affineLineParams ℓ).1 = v 0 / v 1 := by
      simp [affineLineParams, hv1] <;> aesop
    exact h
  have h_v0 : v 0 = a * v 1 := by
    rw [h_a] <;> field_simp [hv1] <;> ring
  have h_b : b = ℓ.offset 0 - a * ℓ.offset 1 := by
    have h : (affineLineParams ℓ).2 = ℓ.offset 0 - (affineLineParams ℓ).1 * ℓ.offset 1 := by
      simp [affineLineParams, hv1] <;> aesop
    exact h
  have h_off_line : ℓ.offset 0 = a * ℓ.offset 1 + b := by linarith [h_b]
  have h_dir_eq : ℓ.1.direction = Submodule.span ℝ {v} := by
    have h_span : Submodule.span ℝ {v} ≤ ℓ.1.direction := by
      apply Submodule.span_le.mpr
      intro x hx
      have h_x_eq : x = v := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]; exact (getDirV_spec ℓ).1
    have h_ne : v ≠ 0 := (getDirV_spec ℓ).2
    have h_finrank1 : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 := finrank_span_singleton h_ne
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v}) = Module.finrank ℝ ℓ.1.direction := by
      rw [h_finrank1, ℓ.2]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h2).symm
  set off_cand : Plane :=
    EuclideanSpace.single 0 (b / (1 + a^2)) +
    EuclideanSpace.single 1 (-a * b / (1 + a^2)) with hcand_def
  have hcand0 : off_cand 0 = b / (1 + a^2) := by
    simp [hcand_def, EuclideanSpace.single_apply] <;> ring
  have hcand1 : off_cand 1 = -a * b / (1 + a^2) := by
    simp [hcand_def, EuclideanSpace.single_apply] <;> ring
  have h1_line : off_cand 0 = a * off_cand 1 + b := by
    rw [hcand0, hcand1] <;> field_simp <;> ring
  let c : ℝ := (off_cand 1 - ℓ.offset 1) / v 1
  have h_comp0 : (off_cand - ℓ.offset) 0 = (c • v) 0 := by
    have h_eq : (off_cand - ℓ.offset) 0 = a * (off_cand 1 - ℓ.offset 1) := by
      simp [h1_line, h_off_line] <;> ring
    rw [h_eq]
    simp [c, h_v0, smul_eq_mul] <;> field_simp [hv1] <;> ring
  have h_comp1 : (off_cand - ℓ.offset) 1 = (c • v) 1 := by
    simp [c, smul_eq_mul] <;> field_simp [hv1] <;> ring
  have h_scalar : off_cand - ℓ.offset = c • v := by
    ext i
    fin_cases i <;> [exact h_comp0; exact h_comp1]
  have h_diff_dir : off_cand - ℓ.offset ∈ ℓ.1.direction := by
    rw [h_dir_eq]
    rw [h_scalar]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have h_off_mem : off_cand ∈ ℓ.1 := by
    have h_vsub : (off_cand -ᵥ ℓ.offset) +ᵥ ℓ.offset = off_cand := by exact AddTorsor.vsub_vadd' off_cand ℓ.offset
    rw [←h_vsub]
    exact AffineSubspace.vadd_mem_of_mem_direction h_diff_dir ℓ.offset_mem
  have h2_orth : ∀ w ∈ ℓ.1.direction, inner ℝ (0 - off_cand) w = 0 := by
    intro w hw
    rw [h_dir_eq] at hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨d, rfl⟩
    have hinner : inner ℝ (0 - off_cand) (d • v) = d * inner ℝ (0 - off_cand) v := by
      rw [inner_smul_right] <;> ring
    rw [hinner]
    have h9 : inner ℝ (0 - off_cand) v = 0 := by
      have h_sum : inner ℝ (0 - off_cand) v = ∑ i : Fin 2, inner ℝ ((0 - off_cand) i) (v i) := PiLp.inner_apply _ _
      rw [h_sum, Fin.sum_univ_two]
      simp [hcand0, hcand1, h_a] <;> field_simp [hv1] <;> ring
    rw [h9] <;> ring
  have h_orth_mem : (0 - off_cand) ∈ ℓ.1.directionᗮ := by
    simp only [Submodule.mem_orthogonal]
    intro u hu
    have h10 : inner ℝ (0 - off_cand) u = 0 := h2_orth u hu
    have h11 : inner ℝ u (0 - off_cand) = inner ℝ (0 - off_cand) u := by exact real_inner_comm (0 - off_cand) u
    rw [h11]
    exact h10
  have h_eq : ℓ.offset = off_cand := by
    have h_iff : EuclideanGeometry.orthogonalProjection ℓ.1 (0 : Plane) = off_cand ↔
        off_cand ∈ ℓ.1 ∧ (0 -ᵥ off_cand) ∈ ℓ.1.directionᗮ :=
      EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem
    have h_main : EuclideanGeometry.orthogonalProjection ℓ.1 (0 : Plane) = off_cand := by
      rw [h_iff]
      exact ⟨h_off_mem, h_orth_mem⟩
    exact h_main
  rw [h_eq]
  exact ⟨hcand0, hcand1⟩

/-- Slope map is 2-Lipschitz: |a₁-a₂| ≤ 2 * dist(ℓ₁,ℓ₂). -/
lemma slope_lipschitz (ℓ₁ ℓ₂ : AffineLine)
    (h1_v1 : (getDirV ℓ₁) 1 ≠ 0)
    (h2_v1 : (getDirV ℓ₂) 1 ≠ 0)
    (h1_slope : |(affineLineParams ℓ₁).1| ≤ 1)
    (h2_slope : |(affineLineParams ℓ₂).1| ≤ 1) :
    |(affineLineParams ℓ₁).1 - (affineLineParams ℓ₂).1| ≤ 2 * AffineLine.dist ℓ₁ ℓ₂ := by
  let a1 := (affineLineParams ℓ₁).1
  let a2 := (affineLineParams ℓ₂).1
  let P1 := ℓ₁.1.direction.starProjection
  let P2 := ℓ₂.1.direction.starProjection
  have hP1 := starProjection_e2_semicircle ℓ₁ h1_v1
  have hP2 := starProjection_e2_semicircle ℓ₂ h2_v1
  have h_denom_le : (1 + a1^2) * (1 + a2^2) ≤ 4 := by
    have h1 : a1^2 ≤ 1 := by nlinarith [abs_le.mp h1_slope]
    have h2 : a2^2 ≤ 1 := by nlinarith [abs_le.mp h2_slope]
    nlinarith
  have h_denom_pos : 0 < (1 + a1^2) * (1 + a2^2) := by positivity
  have h_norm2 : ‖(P1 - P2) e2‖ ^ 2 =
      (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) := by
    have h_sub : (P1 - P2) e2 = P1 e2 - P2 e2 := by rfl
    have h_image0 : ((P1 - P2) e2) 0 = a1 / (1 + a1^2) - a2 / (1 + a2^2) := by
      rw [h_sub]
      have h : (P1 e2 - P2 e2) 0 = (P1 e2) 0 - (P2 e2) 0 := by simp
      rw [h, hP1.1, hP2.1] <;> rfl
    have h_image1 : ((P1 - P2) e2) 1 = 1 / (1 + a1^2) - 1 / (1 + a2^2) := by
      rw [h_sub]
      have h : (P1 e2 - P2 e2) 1 = (P1 e2) 1 - (P2 e2) 1 := by simp
      rw [h, hP1.2, hP2.2] <;> rfl
    rw [EuclideanSpace.real_norm_sq_eq ((P1 - P2) e2), Fin.sum_univ_two, h_image0, h_image1]
    <;> exact semicircle_chord_algebraic a1 a2
  have h4 : ‖(P1 - P2) e2‖ ^ 2 ≥ (a1 - a2)^2 / 4 := by
    rw [h_norm2]
    have h5 : (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) ≥ (a1 - a2)^2 / 4 := by
      gcongr <;> nlinarith
    exact h5
  have h6 : ‖(P1 - P2) e2‖ ≥ |a1 - a2| / 2 := by
    have h7 : 0 ≤ ‖(P1 - P2) e2‖ := by positivity
    have h8 : |a1 - a2| / 2 ≥ 0 := by positivity
    nlinarith [sq_abs (a1 - a2)]
  have h9 : ‖(P1 - P2) e2‖ ≤ ‖P1 - P2‖ := by
    have h10 : ‖(P1 - P2) e2‖ ≤ ‖P1 - P2‖ * ‖e2‖ := ContinuousLinearMap.le_opNorm (P1 - P2) e2
    rw [e2_norm] at h10 <;> linarith
  have h10 : ‖P1 - P2‖ ≤ AffineLine.dist ℓ₁ ℓ₂ := by
    have h11 : AffineLine.dist ℓ₁ ℓ₂ = ‖P1 - P2‖ + ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    rw [h11]
    exact le_add_of_nonneg_right (by positivity)
  linarith

/-! ### Helper lemma stubs (to be filled by teammates or future work) -/

/-- Unit direction vector from slope: u(a) = (a,1)/√(1+a²). -/
noncomputable def slopeUnitVec (a : ℝ) : Plane :=
  (1 / Real.sqrt (1 + a^2)) • (EuclideanSpace.single 0 a + EuclideanSpace.single 1 1)

lemma slopeUnitVec_norm (a : ℝ) : ‖slopeUnitVec a‖ = 1 := by
  have h_pos : 0 < 1 + a^2 := by nlinarith
  have h_sqrt_pos : 0 < Real.sqrt (1 + a^2) := Real.sqrt_pos.mpr h_pos
  let w : Plane := EuclideanSpace.single 0 a + EuclideanSpace.single 1 1
  have hw_norm2 : ‖w‖ ^ 2 = 1 + a^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    simp [w, EuclideanSpace.single_apply] <;> ring
  have h1 : ‖slopeUnitVec a‖ = |(1 / Real.sqrt (1 + a^2))| * ‖w‖ := norm_smul _ _
  have h2 : |(1 / Real.sqrt (1 + a^2))| = 1 / Real.sqrt (1 + a^2) := by
    apply abs_of_pos; positivity
  rw [h1, h2]
  have h3 : ‖w‖ = Real.sqrt (1 + a^2) := by
    have h4 : 0 ≤ ‖w‖ := by positivity
    nlinarith [hw_norm2, Real.sq_sqrt (show 0 ≤ 1 + a^2 by nlinarith)]
  rw [h3]
  field_simp [h_sqrt_pos.ne'] <;> ring

lemma slopeUnitVec_dist (a1 a2 : ℝ) : ‖slopeUnitVec a1 - slopeUnitVec a2‖ ≤ |a1 - a2| := by
  set u1 := slopeUnitVec a1 with hu1
  set u2 := slopeUnitVec a2 with hu2
  set s1 := Real.sqrt (1 + a1^2) with hs1
  set s2 := Real.sqrt (1 + a2^2) with hs2
  set D := s1 * s2 with hD
  have hs1_pos : 0 < s1 := by positivity
  have hs2_pos : 0 < s2 := by positivity
  have hD_pos : 0 < D := mul_pos hs1_pos hs2_pos
  have hD2 : D^2 = (1 + a1^2) * (1 + a2^2) := by
    simp only [hD, hs1, hs2]
    have h : (Real.sqrt (1 + a1^2) * Real.sqrt (1 + a2^2))^2 = (1 + a1^2) * (1 + a2^2) := by
      rw [mul_pow, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)] <;> ring
    exact h
  have hD_ge1 : D ≥ 1 := by
    have h : D^2 ≥ 1 := by rw [hD2]; nlinarith
    nlinarith [hD_pos]
  have h_abs_sq : D^2 - (|a1 * a2| + 1)^2 = (|a1| - |a2|)^2 := by
    have h1 : |a1 * a2| = |a1| * |a2| := by rw [abs_mul]
    have h2 : D^2 - (|a1| * |a2| + 1)^2 = (|a1| - |a2|)^2 := by
      rw [hD2]
      have h3 : |a1| ^ 2 = a1 ^ 2 := by simp [sq_abs]
      have h4 : |a2| ^ 2 = a2 ^ 2 := by simp [sq_abs]
      nlinarith [sq_nonneg (|a1| - |a2|)]
    simpa [h1] using h2
  have h_D_ge_abs : D ≥ |a1 * a2| + 1 := by
    have h4 : D^2 - (|a1 * a2| + 1)^2 ≥ 0 := by
      rw [h_abs_sq]; exact sq_nonneg _
    have h5 : 0 ≤ D := by positivity
    have h6 : 0 ≤ |a1 * a2| + 1 := by positivity
    nlinarith
  have h_sum_ge2 : D + a1 * a2 + 1 ≥ 2 := by
    have h7 : |a1 * a2| + a1 * a2 ≥ 0 := by
      cases' abs_cases (a1 * a2) with h8 h8 <;> linarith
    linarith [h_D_ge_abs]
  have h_denom_ge2 : D * (D + a1 * a2 + 1) ≥ 2 := by
    have h9 : D ≥ 1 := hD_ge1
    nlinarith
  have h_sum_pos : 0 < D + a1 * a2 + 1 := by linarith [h_sum_ge2]
  have h_u1_norm : ‖u1‖ = 1 := slopeUnitVec_norm a1
  have h_u2_norm : ‖u2‖ = 1 := slopeUnitVec_norm a2
  set w1 : Plane := EuclideanSpace.single 0 a1 + EuclideanSpace.single 1 1 with hw1
  set w2 : Plane := EuclideanSpace.single 0 a2 + EuclideanSpace.single 1 1 with hw2
  have h_u1_eq : u1 = (1 / s1) • w1 := by
    have h : slopeUnitVec a1 = (1 / s1) • w1 := by
      simp [slopeUnitVec, hs1, hw1] <;> rfl
    exact hu1 ▸ h
  have h_u2_eq : u2 = (1 / s2) • w2 := by
    have h : slopeUnitVec a2 = (1 / s2) • w2 := by
      simp [slopeUnitVec, hs2, hw2] <;> rfl
    exact hu2 ▸ h
  have h_inner_w : inner ℝ w1 w2 = a1 * a2 + 1 := by
    have h_sum : inner ℝ w1 w2 = ∑ i : Fin 2, inner ℝ (w1 i) (w2 i) := PiLp.inner_apply w1 w2
    rw [h_sum, Fin.sum_univ_two]
    simp [hw1, hw2, EuclideanSpace.single_apply] <;> ring
  have h_inner : inner ℝ u1 u2 = (a1 * a2 + 1) / D := by
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
  have h_id1 : D^2 - (a1 * a2 + 1)^2 = (a1 - a2)^2 := by
    rw [hD2] <;> ring
  have h5 : D - (a1 * a2 + 1) = (a1 - a2)^2 / (D + a1 * a2 + 1) := by
    have h6 : (D - (a1 * a2 + 1)) * (D + a1 * a2 + 1) = (a1 - a2)^2 := by
      linarith [h_id1]
    field_simp [h_sum_pos.ne'] <;> linarith
  have h_final : ‖u1 - u2‖ ^ 2 = 2 * (a1 - a2)^2 / (D * (D + a1 * a2 + 1)) := by
    rw [h_norm2, h_inner]
    have h7 : 2 - 2 * ((a1 * a2 + 1) / D) = 2 * (D - (a1 * a2 + 1)) / D := by
      field_simp [hD_pos.ne'] <;> ring
    rw [h7]
    have h8 : 2 * (D - (a1 * a2 + 1)) / D = 2 * (a1 - a2)^2 / (D * (D + a1 * a2 + 1)) := by
      rw [h5]
      field_simp [hD_pos.ne', h_sum_pos.ne'] <;> ring
    exact h8
  have h6 : ‖u1 - u2‖ ^ 2 ≤ (a1 - a2)^2 := by
    rw [h_final]
    have h7 : 0 ≤ (a1 - a2)^2 := by positivity
    have h8 : 0 < D * (D + a1 * a2 + 1) := by positivity
    have h9 : 2 ≤ D * (D + a1 * a2 + 1) := h_denom_ge2
    have h10 : 2 * (a1 - a2)^2 / (D * (D + a1 * a2 + 1)) ≤ (a1 - a2)^2 := by
      calc 2 * (a1 - a2)^2 / (D * (D + a1 * a2 + 1))
          = (2 / (D * (D + a1 * a2 + 1))) * (a1 - a2)^2 := by ring
      _ ≤ 1 * (a1 - a2)^2 := by
        gcongr
        have h11 : 2 / (D * (D + a1 * a2 + 1)) ≤ 1 := by
          apply (div_le_one (by positivity)).mpr
          exact h9
        exact h11
      _ = (a1 - a2)^2 := by ring
    exact h10
  have h11 : (a1 - a2)^2 = |a1 - a2|^2 := by rw [sq_abs]
  rw [h11] at h6
  have h12 : 0 ≤ ‖u1 - u2‖ := by positivity
  have h13 : 0 ≤ |a1 - a2| := by positivity
  have h14 : |‖u1 - u2‖| = ‖u1 - u2‖ := by rw [abs_of_nonneg h12]
  have h15 : |(|a1 - a2|)| = |a1 - a2| := by rw [abs_of_nonneg h13]
  have h16 : |‖u1 - u2‖| ≤ |(|a1 - a2|)| := sq_le_sq.mp h6
  rw [h14, h15] at h16
  exact h16

/-- Direction projection upper bound: ‖P₁-P₂‖ ≤ 2·|a₁-a₂| for |a|≤1. -/
lemma direction_proj_upper_bound (ℓ₁ ℓ₂ : AffineLine)
    (h1_v1 : (getDirV ℓ₁) 1 ≠ 0)
    (h2_v1 : (getDirV ℓ₂) 1 ≠ 0) :
    ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤
    2 * |(affineLineParams ℓ₁).1 - (affineLineParams ℓ₂).1| := by
  set a1 := (affineLineParams ℓ₁).1 with ha1
  set a2 := (affineLineParams ℓ₂).1 with ha2
  set v1 := getDirV ℓ₁ with hv1_def
  set v2 := getDirV ℓ₂ with hv2_def
  have h_a1 : a1 = v1 0 / v1 1 := by
    simp [ha1, affineLineParams, h1_v1] <;> aesop
  have h_a2 : a2 = v2 0 / v2 1 := by
    simp [ha2, affineLineParams, h2_v1] <;> aesop
  have h_dir1_eq : ℓ₁.1.direction = Submodule.span ℝ {v1} := by
    have h_span : Submodule.span ℝ {v1} ≤ ℓ₁.1.direction := by
      apply Submodule.span_le.mpr
      intro x hx
      have h_x_eq : x = v1 := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]; exact (getDirV_spec ℓ₁).1
    have h_ne : v1 ≠ 0 := (getDirV_spec ℓ₁).2
    have h_finrank1 : Module.finrank ℝ (Submodule.span ℝ {v1}) = 1 := finrank_span_singleton h_ne
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v1}) = Module.finrank ℝ ℓ₁.1.direction := by
      rw [h_finrank1, ℓ₁.2]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h2).symm
  have h_dir2_eq : ℓ₂.1.direction = Submodule.span ℝ {v2} := by
    have h_span : Submodule.span ℝ {v2} ≤ ℓ₂.1.direction := by
      apply Submodule.span_le.mpr
      intro x hx
      have h_x_eq : x = v2 := by simpa [Set.mem_singleton_iff] using hx
      rw [h_x_eq]; exact (getDirV_spec ℓ₂).1
    have h_ne : v2 ≠ 0 := (getDirV_spec ℓ₂).2
    have h_finrank2 : Module.finrank ℝ (Submodule.span ℝ {v2}) = 1 := finrank_span_singleton h_ne
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v2}) = Module.finrank ℝ ℓ₂.1.direction := by
      rw [h_finrank2, ℓ₂.2]
    exact (Submodule.eq_of_le_of_finrank_eq h_span h2).symm
  let u1 := slopeUnitVec a1
  let u2 := slopeUnitVec a2
  let s1 := Real.sqrt (1 + a1^2)
  let s2 := Real.sqrt (1 + a2^2)
  have hs1_pos : 0 < s1 := by positivity
  have hs2_pos : 0 < s2 := by positivity
  have h_v1_scalar : v1 = (v1 1 * s1) • u1 := by
    have h_v0 : v1 0 = a1 * v1 1 := by
      rw [h_a1] <;> field_simp [h1_v1] <;> ring
    ext i
    fin_cases i
    · simp [h_v0, u1, slopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul] <;> field_simp [h1_v1, hs1_pos.ne'] <;> ring
    · simp [u1, slopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul] <;> field_simp [h1_v1, hs1_pos.ne'] <;> ring
  have h_v2_scalar : v2 = (v2 1 * s2) • u2 := by
    have h_v0 : v2 0 = a2 * v2 1 := by
      rw [h_a2] <;> field_simp [h2_v1] <;> ring
    ext i
    fin_cases i
    · simp [h_v0, u2, slopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul] <;> field_simp [h2_v1, hs2_pos.ne'] <;> ring
    · simp [u2, slopeUnitVec, EuclideanSpace.single_apply, smul_eq_mul] <;> field_simp [h2_v1, hs2_pos.ne'] <;> ring
  let c1 := v1 1 * s1
  let c2 := v2 1 * s2
  have h_c1_ne_zero : c1 ≠ 0 := by
    simp [c1, h1_v1, hs1_pos.ne'] <;> exact h1_v1
  have h_c2_ne_zero : c2 ≠ 0 := by
    simp [c2, h2_v1, hs2_pos.ne'] <;> exact h2_v1
  have h_isUnit1 : IsUnit c1 := IsUnit.mk0 c1 h_c1_ne_zero
  have h_isUnit2 : IsUnit c2 := IsUnit.mk0 c2 h_c2_ne_zero
  have h_span1 : Submodule.span ℝ {v1} = Submodule.span ℝ {u1} := by
    rw [h_v1_scalar]
    exact Submodule.span_singleton_smul_eq h_isUnit1 u1
  have h_span2 : Submodule.span ℝ {v2} = Submodule.span ℝ {u2} := by
    rw [h_v2_scalar]
    exact Submodule.span_singleton_smul_eq h_isUnit2 u2
  let P1 := Submodule.starProjection (Submodule.span ℝ {u1})
  let P2 := Submodule.starProjection (Submodule.span ℝ {u2})
  have h_proj1_eq : ℓ₁.1.direction.starProjection = P1 := by
    rw [h_dir1_eq, h_span1]
  have h_proj2_eq : ℓ₂.1.direction.starProjection = P2 := by
    rw [h_dir2_eq, h_span2]
  rw [h_proj1_eq, h_proj2_eq]
  have h_u1_norm : ‖u1‖ = 1 := slopeUnitVec_norm a1
  have h_u2_norm : ‖u2‖ = 1 := slopeUnitVec_norm a2
  have h_bound : ∀ (x : Plane), ‖(P1 - P2) x‖ ≤ 2 * ‖u1 - u2‖ * ‖x‖ := by
    intro x
    have h1 : P1 x = inner ℝ x u1 • u1 := by
      have h := Submodule.starProjection_unit_singleton ℝ h_u1_norm x
      have h_comm : inner ℝ u1 x = inner ℝ x u1 := by exact real_inner_comm x u1
      rw [h_comm] at h; exact h
    have h2 : P2 x = inner ℝ x u2 • u2 := by
      have h := Submodule.starProjection_unit_singleton ℝ h_u2_norm x
      have h_comm : inner ℝ u2 x = inner ℝ x u2 := by exact real_inner_comm x u2
      rw [h_comm] at h; exact h
    have h3 : (P1 - P2) x = (inner ℝ x u1 • u1) - (inner ℝ x u2 • u2) := by
      simp [h1, h2]
    rw [h3]
    have h4 : (inner ℝ x u1 • u1) - (inner ℝ x u2 • u2) =
        (inner ℝ x u1) • (u1 - u2) + (inner ℝ x (u1 - u2)) • u2 := by
      have h5 : inner ℝ x (u1 - u2) = inner ℝ x u1 - inner ℝ x u2 := by
        rw [← inner_sub_right] <;> rfl
      apply Eq.symm
      calc (inner ℝ x u1) • (u1 - u2) + (inner ℝ x (u1 - u2)) • u2
          = (inner ℝ x u1) • u1 - (inner ℝ x u1) • u2 + (inner ℝ x (u1 - u2)) • u2 := by
            rw [smul_sub]
      _ = (inner ℝ x u1) • u1 - (inner ℝ x u1) • u2 + ((inner ℝ x u1) - (inner ℝ x u2)) • u2 := by
            rw [h5]
      _ = (inner ℝ x u1) • u1 - (inner ℝ x u2) • u2 := by rw [sub_smul] <;> abel
      _ = (inner ℝ x u1 • u1) - (inner ℝ x u2 • u2) := by rfl
    rw [h4]
    calc ‖(inner ℝ x u1) • (u1 - u2) + (inner ℝ x (u1 - u2)) • u2‖
        ≤ ‖(inner ℝ x u1) • (u1 - u2)‖ + ‖(inner ℝ x (u1 - u2)) • u2‖ := norm_add_le _ _
      _ = |inner ℝ x u1| * ‖u1 - u2‖ + |inner ℝ x (u1 - u2)| * ‖u2‖ := by
        simp [norm_smul] <;> ring
      _ ≤ ‖x‖ * ‖u1‖ * ‖u1 - u2‖ + ‖x‖ * ‖u1 - u2‖ * ‖u2‖ := by
        have h5 : |inner ℝ x u1| ≤ ‖x‖ * ‖u1‖ := abs_real_inner_le_norm x u1
        have h6 : |inner ℝ x (u1 - u2)| ≤ ‖x‖ * ‖u1 - u2‖ := abs_real_inner_le_norm x (u1 - u2)
        gcongr <;> linarith
      _ = 2 * ‖u1 - u2‖ * ‖x‖ := by rw [h_u1_norm, h_u2_norm] <;> ring
  have h_op_norm : ‖P1 - P2‖ ≤ 2 * ‖u1 - u2‖ :=
    ContinuousLinearMap.opNorm_le_bound (P1 - P2) (by positivity) h_bound
  have h_dist : ‖u1 - u2‖ ≤ |a1 - a2| := slopeUnitVec_dist a1 a2
  linarith

/-- Tight offset difference bound: ‖off₁-off₂‖ ≤ B·|a₁-a₂| + |b₁-b₂|. -/
lemma offset_diff_bound_tight {a1 b1 a2 b2 B : ℝ}
    (hb2 : |b2| ≤ B) (hB : 0 ≤ B)
    (off1 off2 : Plane)
    (h11 : off1 0 = b1 / (1 + a1^2))
    (h12 : off1 1 = -a1 * b1 / (1 + a1^2))
    (h21 : off2 0 = b2 / (1 + a2^2))
    (h22 : off2 1 = -a2 * b2 / (1 + a2^2)) :
    ‖off1 - off2‖ ≤ B * |a1 - a2| + |b1 - b2| := by
  let f : ℝ → Plane := fun a =>
    EuclideanSpace.single 0 (1 / (1 + a^2)) +
    EuclideanSpace.single 1 (-a / (1 + a^2))
  have hf1 : off1 = b1 • f a1 := by
    ext i
    fin_cases i <;> simp [h11, h12, f, EuclideanSpace.single_apply, smul_eq_mul] <;> ring
  have hf2 : off2 = b2 • f a2 := by
    ext i
    fin_cases i <;> simp [h21, h22, f, EuclideanSpace.single_apply, smul_eq_mul] <;> ring
  have h_f_norm : ∀ a : ℝ, ‖f a‖ ≤ 1 := by
    intro a
    have h_pos : 0 < 1 + a^2 := by nlinarith
    have h_sq : ‖f a‖ ^ 2 = 1 / (1 + a^2) := by
      simp [f, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, EuclideanSpace.single_apply]
      <;> field_simp <;> ring
    have h_le : 1 / (1 + a^2) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith
    have h : ‖f a‖ ^ 2 ≤ 1 := by
      rw [h_sq]; exact h_le
    have h_nonneg : 0 ≤ ‖f a‖ := by positivity
    nlinarith
  have h_f_diff : ‖f a1 - f a2‖ ≤ |a1 - a2| := by
    have h_expand : ‖f a1 - f a2‖ ^ 2 =
        (1 / (1 + a1^2) - 1 / (1 + a2^2))^2 +
        ((-a1 / (1 + a1^2)) - (-a2 / (1 + a2^2)))^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      <;> simp [f, EuclideanSpace.single_apply] <;> ring
    have h_sq : ‖f a1 - f a2‖ ^ 2 = (a1 - a2)^2 / ((1 + a1^2) * (1 + a2^2)) := by
      rw [h_expand]
      have h_comm : (1 / (1 + a1^2) - 1 / (1 + a2^2))^2 +
          ((-a1 / (1 + a1^2)) - (-a2 / (1 + a2^2)))^2 =
          (a1 / (1 + a1^2) - a2 / (1 + a2^2))^2 +
          (1 / (1 + a1^2) - 1 / (1 + a2^2))^2 := by ring
      rw [h_comm]
      exact semicircle_chord_algebraic a1 a2
    have h_pos : 0 < (1 + a1^2) * (1 + a2^2) := by positivity
    have h_ge : 1 ≤ (1 + a1^2) * (1 + a2^2) := by nlinarith
    have h : ‖f a1 - f a2‖ ^ 2 ≤ (a1 - a2)^2 := by
      rw [h_sq]
      exact (div_le_self (by positivity) h_ge)
    have h_nonneg : 0 ≤ ‖f a1 - f a2‖ := by positivity
    have h_nonneg1 : 0 ≤ ‖f a1 - f a2‖ := by positivity
    have h_nonneg2 : 0 ≤ |a1 - a2| := by positivity
    have h_abs : (a1 - a2)^2 = |a1 - a2|^2 := by rw [sq_abs]
    rw [h_abs] at h
    nlinarith
  have h_decomp : off1 - off2 = b2 • (f a1 - f a2) + (b1 - b2) • f a1 := by
    rw [hf1, hf2]
    have h_smul_sub : b2 • (f a1 - f a2) = b2 • f a1 - b2 • f a2 := by rw [smul_sub]
    have h_smul_diff : (b1 - b2) • f a1 = b1 • f a1 - b2 • f a1 := by rw [sub_smul]
    have h : b1 • f a1 - b2 • f a2 = b2 • (f a1 - f a2) + (b1 - b2) • f a1 := by
      rw [h_smul_sub, h_smul_diff] <;> abel
    exact h
  rw [h_decomp]
  have h1 : ‖b2 • (f a1 - f a2) + (b1 - b2) • f a1‖
      ≤ ‖b2 • (f a1 - f a2)‖ + ‖(b1 - b2) • f a1‖ := norm_add_le _ _
  have h2 : ‖b2 • (f a1 - f a2)‖ + ‖(b1 - b2) • f a1‖
      = |b2| * ‖f a1 - f a2‖ + |b1 - b2| * ‖f a1‖ := by
    simp [norm_smul] <;> ring
  have h3 : |b2| * ‖f a1 - f a2‖ + |b1 - b2| * ‖f a1‖
      ≤ |b2| * |a1 - a2| + |b1 - b2| * 1 := by
    calc |b2| * ‖f a1 - f a2‖ + |b1 - b2| * ‖f a1‖
        ≤ |b2| * |a1 - a2| + |b1 - b2| * ‖f a1‖ := by gcongr
      _ ≤ |b2| * |a1 - a2| + |b1 - b2| * 1 := by gcongr <;> exact h_f_norm a1
  have h4 : |b2| * |a1 - a2| + |b1 - b2| * 1 ≤ B * |a1 - a2| + |b1 - b2| := by
    calc |b2| * |a1 - a2| + |b1 - b2| * 1
        ≤ B * |a1 - a2| + |b1 - b2| * 1 := by gcongr <;> exact hb2
      _ = B * |a1 - a2| + |b1 - b2| := by ring
  linarith

/-- Near-point intercept bound: if p is within δ of line x = a*y + b,
    then |b - (p₀ - a*p₁)| ≤ 2*δ. -/
lemma near_point_intercept_bound {a b δ : ℝ} {p : Plane}
    (hδ_pos : 0 < δ) (ha_slope : |a| ≤ 1)
    (h_near : p ∈ Metric.cthickening δ (appendixDualLine a b)) :
    |b - (p 0 - a * p 1)| ≤ 2 * δ := by
  have hε : 0 ≤ δ := by linarith
  have h_closed : IsClosed (appendixDualLine a b : Set Plane) := by
    have h_cont : Continuous (fun p : Plane => p 0 - a * p 1) := by fun_prop
    have h_eq : appendixDualLine a b = (fun p : Plane => p 0 - a * p 1) ⁻¹' {b} := by
      ext z
      simp only [appendixDualLine, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
      <;> constructor <;> intro h <;> linarith
    rw [h_eq]
    exact IsClosed.preimage h_cont isClosed_singleton
  have h_nonempty : (appendixDualLine a b : Set Plane).Nonempty := by
    let q : Plane := EuclideanSpace.single 0 b
    have hq' : q 0 = a * q 1 + b := by
      simp [q, EuclideanSpace.single_apply] <;> ring
    have hqS : q ∈ appendixDualLine a b := by
      simpa [appendixDualLine, Set.mem_setOf_eq] using hq'
    exact ⟨q, hqS⟩
  have h_eq : Metric.cthickening δ (appendixDualLine a b : Set Plane) =
      ⋃ x ∈ (appendixDualLine a b : Set Plane), Metric.closedBall x δ := by
    rw [Metric.cthickening_eq_biUnion_closedBall (appendixDualLine a b : Set Plane) hε]
    rw [h_closed.closure_eq]
  rw [h_eq] at h_near
  have h_exists : ∃ (q : Plane), q ∈ appendixDualLine a b ∧ p ∈ Metric.closedBall q δ := by
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using h_near
  rcases h_exists with ⟨q, hq_line, hq_ball⟩
  have hq_eq : q 0 = a * q 1 + b := by
    simpa [appendixDualLine, Set.mem_setOf_eq] using hq_line
  have h_dist : dist p q ≤ δ := by simpa [Metric.mem_closedBall] using hq_ball
  have h_dx : |p 0 - q 0| ≤ δ := by
    have h2 : |(p - q) 0| ≤ ‖p - q‖ := by
      have h3 : ‖p - q‖ ^ 2 = ∑ j : Fin 2, ((p - q) j)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq] <;> rfl
      have h4 : ((p - q) 0)^2 ≤ ‖p - q‖ ^ 2 := by
        rw [h3]
        exact Finset.single_le_sum (f := fun j : Fin 2 => ((p - q) j)^2) (fun j _ => by positivity) (Finset.mem_univ 0)
      have h5 : 0 ≤ |(p - q) 0| := by positivity
      have h6 : 0 ≤ ‖p - q‖ := by positivity
      nlinarith [sq_abs ((p - q) 0)]
    have h7 : (p - q) 0 = p 0 - q 0 := by rfl
    rw [h7] at h2
    have h8 : ‖p - q‖ = dist p q := by rw [dist_eq_norm]
    rw [h8] at h2
    exact le_trans h2 h_dist
  have h_dy : |p 1 - q 1| ≤ δ := by
    have h2 : |(p - q) 1| ≤ ‖p - q‖ := by
      have h3 : ‖p - q‖ ^ 2 = ∑ j : Fin 2, ((p - q) j)^2 := by
        rw [EuclideanSpace.real_norm_sq_eq] <;> rfl
      have h4 : ((p - q) 1)^2 ≤ ‖p - q‖ ^ 2 := by
        rw [h3]
        exact Finset.single_le_sum (f := fun j : Fin 2 => ((p - q) j)^2) (fun j _ => by positivity) (Finset.mem_univ 1)
      have h5 : 0 ≤ |(p - q) 1| := by positivity
      have h6 : 0 ≤ ‖p - q‖ := by positivity
      nlinarith [sq_abs ((p - q) 1)]
    have h7 : (p - q) 1 = p 1 - q 1 := by rfl
    rw [h7] at h2
    have h8 : ‖p - q‖ = dist p q := by rw [dist_eq_norm]
    rw [h8] at h2
    exact le_trans h2 h_dist
  have h3 : p 0 - a * p 1 - b = (p 0 - q 0) - a * (p 1 - q 1) := by
    rw [hq_eq] <;> ring
  have h8 : |p 0 - a * p 1 - b| ≤ (1 + |a|) * δ := by
    rw [h3]
    have h9 : |(p 0 - q 0) - a * (p 1 - q 1)| ≤ |p 0 - q 0| + |a| * |p 1 - q 1| := by
      calc |(p 0 - q 0) - a * (p 1 - q 1)|
        ≤ |p 0 - q 0| + |a * (p 1 - q 1)| := by exact abs_sub (p.ofLp 0 - q.ofLp 0) (a * (p.ofLp 1 - q.ofLp 1))
      _ = |p 0 - q 0| + |a| * |p 1 - q 1| := by rw [abs_mul]
    have h10 : |p 0 - q 0| + |a| * |p 1 - q 1| ≤ (1 + |a|) * δ := by
      calc |p 0 - q 0| + |a| * |p 1 - q 1|
        ≤ δ + |a| * δ := by gcongr
      _ = (1 + |a|) * δ := by ring
    exact h9.trans h10
  have h11 : (1 + |a|) * δ ≤ 2 * δ := by
    have h12 : 1 + |a| ≤ 2 := by linarith [abs_le.mp ha_slope]
    gcongr
  have h13 : |b - (p 0 - a * p 1)| = |p 0 - a * p 1 - b| := by
    have h14 : b - (p 0 - a * p 1) = -(p 0 - a * p 1 - b) := by ring
    rw [h14, abs_neg]
  rw [h13]
  exact h8.trans h11

/-- Coordinate absolute value bounded by norm. -/
lemma coord_abs_le_norm (x : Plane) (i : Fin 2) : |x i| ≤ ‖x‖ := by
  have h2 : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
  have h1 : (x i)^2 ≤ ‖x‖ ^ 2 := by
    rw [h2]
    fin_cases i <;> simp [sq_nonneg] <;> nlinarith
  have h4 : 0 ≤ ‖x‖ := by positivity
  have h5 : 0 ≤ |x i| := by positivity
  nlinarith [sq_abs (x i)]

/-- From cthickening membership to infDist bound. -/
lemma cthickening_to_infDist {p : Plane} {s : Set Plane} {δ : ℝ}
    (hδ_pos : 0 < δ) (h_nonempty : s.Nonempty)
    (h_near : p ∈ Metric.cthickening δ s) :
    Metric.infDist p s ≤ δ := by
  have h4 : Metric.infEDist p s ≤ ENNReal.ofReal δ := h_near
  have hb : (ENNReal.ofReal δ) ≠ ⊤ := by simp
  have ha : Metric.infEDist p s ≠ ⊤ := ne_top_of_le_ne_top hb h4
  have h5 : (Metric.infEDist p s).toReal ≤ (ENNReal.ofReal δ).toReal :=
    (ENNReal.toReal_le_toReal ha hb).mpr h4
  have h6 : (ENNReal.ofReal δ).toReal = δ := by
    rw [ENNReal.toReal_ofReal (by linarith)]
  rw [h6] at h5
  simpa [Metric.infDist] using h5

/-- Near-point intercept bound for AffineLine directly. -/
lemma near_point_intercept_bound_affine {ℓ : AffineLine} {p : Plane} {δ : ℝ}
    (hδ_pos : 0 < δ) (ha_slope : |(affineLineParams ℓ).1| ≤ 1)
    (hv1 : (getDirV ℓ) 1 ≠ 0)
    (h_near : p ∈ Metric.cthickening δ (ℓ.1 : Set Plane)) :
    |(affineLineParams ℓ).2 - (p 0 - (affineLineParams ℓ).1 * p 1)| ≤ 2 * δ := by
  let a := (affineLineParams ℓ).1
  let b := (affineLineParams ℓ).2
  have h_closed : IsClosed (ℓ.1 : Set Plane) :=
    AffineSubspace.closed_of_finiteDimensional (ℓ.1)
  have h_nonempty : (ℓ.1 : Set Plane).Nonempty := ℓ.nonempty
  have h_infDist : Metric.infDist p (ℓ.1 : Set Plane) ≤ δ :=
    cthickening_to_infDist hδ_pos h_nonempty h_near
  rcases h_closed.exists_infDist_eq_dist h_nonempty p with ⟨q, hq, h_eq⟩
  have hdist : dist p q ≤ δ := by rw [←h_eq]; exact h_infDist
  have hq_line : q 0 = a * q 1 + b := affineLineParams_correct ℓ hv1 q hq
  have h3 : p 0 - a * p 1 - b = (p 0 - q 0) - a * (p 1 - q 1) := by
    rw [hq_line] <;> ring
  have h4 : |p 0 - q 0| ≤ dist p q := by
    have h5 : |p 0 - q 0| ≤ ‖p - q‖ := coord_abs_le_norm (p - q) 0
    simpa [dist_eq_norm] using h5
  have h6 : |p 1 - q 1| ≤ dist p q := by
    have h7 : |p 1 - q 1| ≤ ‖p - q‖ := coord_abs_le_norm (p - q) 1
    simpa [dist_eq_norm] using h7
  have h8 : |p 0 - a * p 1 - b| ≤ (1 + |a|) * δ := by
    rw [h3]
    have h9 : |(p 0 - q 0) - a * (p 1 - q 1)| ≤ |p 0 - q 0| + |a| * |p 1 - q 1| := by
      calc |(p 0 - q 0) - a * (p 1 - q 1)|
        ≤ |p 0 - q 0| + |a * (p 1 - q 1)| := by exact abs_sub (p.ofLp 0 - q.ofLp 0) (a * (p.ofLp 1 - q.ofLp 1))
      _ = |p 0 - q 0| + |a| * |p 1 - q 1| := by rw [abs_mul]
    have h10 : |p 0 - q 0| + |a| * |p 1 - q 1| ≤ (1 + |a|) * dist p q := by
      calc |p 0 - q 0| + |a| * |p 1 - q 1|
        ≤ dist p q + |a| * dist p q := by gcongr
      _ = (1 + |a|) * dist p q := by ring
    exact h9.trans (h10.trans (by gcongr))
  have h11 : (1 + |a|) * δ ≤ 2 * δ := by
    have h12 : 1 + |a| ≤ 2 := by linarith [abs_le.mp ha_slope]
    gcongr
  have h13 : |b - (p 0 - a * p 1)| = |p 0 - a * p 1 - b| := by
    have h14 : b - (p 0 - a * p 1) = -(p 0 - a * p 1 - b) := by ring
    rw [h14, abs_neg]
  rw [h13]
  exact h8.trans h11

/-- Bound on intercept difference for two lines near p. -/
lemma intercept_diff_bound (ℓ₁ ℓ₂ : AffineLine) (p : Plane) (δ : ℝ)
    (hδ_pos : 0 < δ) (hp : p ∈ Metric.closedBall 0 1)
    (h_near1 : p ∈ Metric.cthickening δ (ℓ₁.1 : Set Plane))
    (h_near2 : p ∈ Metric.cthickening δ (ℓ₂.1 : Set Plane))
    (h1_v1 : (getDirV ℓ₁) 1 ≠ 0) (h2_v1 : (getDirV ℓ₂) 1 ≠ 0)
    (h_slope1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (h_slope2 : |(affineLineParams ℓ₂).1| ≤ 1) :
    |(affineLineParams ℓ₁).2 - (affineLineParams ℓ₂).2| ≤
    4 * δ + |(affineLineParams ℓ₁).1 - (affineLineParams ℓ₂).1| := by
  set a1 := (affineLineParams ℓ₁).1 with ha1
  set b1 := (affineLineParams ℓ₁).2 with hb1
  set a2 := (affineLineParams ℓ₂).1 with ha2
  set b2 := (affineLineParams ℓ₂).2 with hb2
  have h_p1 : |p 1| ≤ 1 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
    have h4 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
    linarith
  let x1 := p 0 - a1 * p 1
  let x2 := p 0 - a2 * p 1
  have h1 : |b1 - x1| ≤ 2 * δ :=
    near_point_intercept_bound_affine hδ_pos h_slope1 h1_v1 h_near1
  have h2 : |b2 - x2| ≤ 2 * δ :=
    near_point_intercept_bound_affine hδ_pos h_slope2 h2_v1 h_near2
  have h2' : |x2 - b2| ≤ 2 * δ := by
    have h2'' : |x2 - b2| = |b2 - x2| := by rw [abs_sub_comm]
    rw [h2'']; exact h2
  have h4 : |x1 - x2| = |a1 - a2| * |p 1| := by
    have h5 : x1 - x2 = (a2 - a1) * p 1 := by simp [x1, x2] <;> ring
    rw [h5, abs_mul]
    have h6 : |a2 - a1| = |a1 - a2| := by
      rw [show a2 - a1 = -(a1 - a2) by ring, abs_neg]
    rw [h6] <;> ring
  have h5 : |a1 - a2| * |p 1| ≤ |a1 - a2| := by
    have h6 : 0 ≤ |a1 - a2| := by positivity
    nlinarith [h_p1]
  have h_main : |b1 - b2| ≤ |b1 - x1| + |x1 - x2| + |x2 - b2| := by
    have h7 : b1 - b2 = (b1 - x1) + (x1 - x2) + (x2 - b2) := by ring
    rw [h7]
    have h8 : |(b1 - x1) + (x1 - x2) + (x2 - b2)| ≤
        |b1 - x1| + |x1 - x2| + |x2 - b2| := by
      calc
        _ ≤ |(b1 - x1) + (x1 - x2)| + |x2 - b2| := by exact abs_add_le (b1 - x1 + (x1 - x2)) (x2 - b2)
      _ ≤ |b1 - x1| + |x1 - x2| + |x2 - b2| := by gcongr; exact abs_add_le (b1 - x1) (x1 - x2)
    exact h8
  rw [h4] at h_main
  linarith [h1, h2', h5]

/-- Bound on |b| for a line near p in unit ball. -/
lemma b_bound (ℓ : AffineLine) (p : Plane) (δ : ℝ)
    (hδ_pos : 0 < δ) (hp : p ∈ Metric.closedBall 0 1)
    (h_near : p ∈ Metric.cthickening δ (ℓ.1 : Set Plane))
    (hv1 : (getDirV ℓ) 1 ≠ 0)
    (h_slope : |(affineLineParams ℓ).1| ≤ 1) :
    |(affineLineParams ℓ).2| ≤ 2 + 2 * δ := by
  let a := (affineLineParams ℓ).1
  let b := (affineLineParams ℓ).2
  have h_p0 : |p 0| ≤ 1 := by
    have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm p 0
    have h4 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
    linarith
  have h_p1 : |p 1| ≤ 1 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
    have h4 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
    linarith
  have h1 : |b - (p 0 - a * p 1)| ≤ 2 * δ :=
    near_point_intercept_bound_affine hδ_pos h_slope hv1 h_near
  have h_tri : |b| ≤ |b - (p 0 - a * p 1)| + |p 0 - a * p 1| := by
    have h : |b - (0 : ℝ)| ≤ |b - (p 0 - a * p 1)| + |(p 0 - a * p 1) - (0 : ℝ)| :=
      abs_sub_le b (p 0 - a * p 1) 0
    simpa using h
  have h2 : |b| ≤ |p 0 - a * p 1| + 2 * δ := by
    calc |b|
      ≤ |b - (p 0 - a * p 1)| + |p 0 - a * p 1| := h_tri
    _ ≤ 2 * δ + |p 0 - a * p 1| := by gcongr
    _ = |p 0 - a * p 1| + 2 * δ := by ring
  have h3 : |p 0 - a * p 1| ≤ |p 0| + |a| * |p 1| := by
    calc |p 0 - a * p 1|
      ≤ |p 0| + |a * p 1| := by exact abs_sub (p.ofLp 0) (a * p.ofLp 1)
    _ = |p 0| + |a| * |p 1| := by rw [abs_mul]
  have h4 : |p 0| + |a| * |p 1| ≤ 2 := by
    calc |p 0| + |a| * |p 1|
      ≤ 1 + 1 * 1 := by gcongr <;> linarith [abs_le.mp h_slope]
    _ = 2 := by norm_num
  linarith

/-- Combined distance bound for lines near p ∈ unit ball:
    dist(ℓ₁,ℓ₂) ≤ 30·|a₁-a₂| + 10δ. -/
lemma dist_bound_near_point (ℓ₁ ℓ₂ : AffineLine) (p : Plane) (δ : ℝ)
    (hδ_pos : 0 < δ) (hp : p ∈ Metric.closedBall 0 1)
    (h_near1 : p ∈ Metric.cthickening δ (ℓ₁.1 : Set Plane))
    (h_near2 : p ∈ Metric.cthickening δ (ℓ₂.1 : Set Plane))
    (h1_v1 : (getDirV ℓ₁) 1 ≠ 0) (h2_v1 : (getDirV ℓ₂) 1 ≠ 0)
    (h_slope1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (h_slope2 : |(affineLineParams ℓ₂).1| ≤ 1) :
    AffineLine.dist ℓ₁ ℓ₂ ≤ 30 * |(affineLineParams ℓ₁).1 - (affineLineParams ℓ₂).1| + 10 * δ := by
  set a1 := (affineLineParams ℓ₁).1 with ha1
  set b1 := (affineLineParams ℓ₁).2 with hb1
  set a2 := (affineLineParams ℓ₂).1 with ha2
  set b2 := (affineLineParams ℓ₂).2 with hb2
  let d := |a1 - a2|
  have h_d_nonneg : 0 ≤ d := by positivity
  have h_d_le_two : d ≤ 2 := by
    have h3 : |a1 - a2| ≤ |a1| + |a2| := by
      exact abs_sub a1 a2
    linarith [abs_le.mp h_slope1, abs_le.mp h_slope2]
  have h_dir2 : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ 2 * d :=
    direction_proj_upper_bound ℓ₁ ℓ₂ h1_v1 h2_v1
  have h_dir : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ 3 * d := by
    linarith
  have h_off1 := offset_formula ℓ₁ h1_v1
  have h_off2 := offset_formula ℓ₂ h2_v1
  have h_b2 : |b2| ≤ 2 + 2 * δ :=
    b_bound ℓ₂ p δ hδ_pos hp h_near2 h2_v1 h_slope2
  have h_off : ‖ℓ₁.offset - ℓ₂.offset‖ ≤ (2 + 2 * δ) * d + |b1 - b2| :=
    offset_diff_bound_tight (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2) (B := 2 + 2 * δ)
      h_b2 (by positivity) ℓ₁.offset ℓ₂.offset h_off1.1 h_off1.2 h_off2.1 h_off2.2
  have h_b_diff : |b1 - b2| ≤ 4 * δ + d :=
    intercept_diff_bound ℓ₁ ℓ₂ p δ hδ_pos hp h_near1 h_near2 h1_v1 h2_v1 h_slope1 h_slope2
  have h_main : AffineLine.dist ℓ₁ ℓ₂ ≤ (6 + 2 * δ) * d + 4 * δ := by
    have h_dist_def : AffineLine.dist ℓ₁ ℓ₂ =
        ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
        ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    rw [h_dist_def]
    calc ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
           ‖ℓ₁.offset - ℓ₂.offset‖
        ≤ 3 * d + ((2 + 2 * δ) * d + |b1 - b2|) := by gcongr
      _ = (5 + 2 * δ) * d + |b1 - b2| := by ring
      _ ≤ (5 + 2 * δ) * d + (4 * δ + d) := by gcongr
      _ = (6 + 2 * δ) * d + 4 * δ := by ring
  have h_final : (6 + 2 * δ) * d + 4 * δ ≤ 30 * d + 10 * δ := by
    by_cases h : δ ≤ 12
    · have h5 : (2 * δ - 24) * d ≤ 0 := by
        have h6 : 2 * δ - 24 ≤ 0 := by linarith
        have h7 : 0 ≤ d := by positivity
        nlinarith
      linarith
    · have hδ_gt : 12 < δ := by linarith
      have h5 : (2 * δ - 24) * d ≤ 6 * δ := by
        have h6 : (2 * δ - 24) * d ≤ (2 * δ - 24) * 2 := by gcongr <;> linarith
        have h7 : (2 * δ - 24) * 2 ≤ 6 * δ := by linarith
        linarith
      linarith
  exact h_main.trans h_final

/-! ### R2 variants: work for ‖p‖ ≤ 2 instead of p ∈ closedBall 0 1 -/

/-- Bound on |b| for a line near p with ‖p‖ ≤ 2. -/
lemma b_bound_R2 (ℓ : AffineLine) (p : Plane) (δ : ℝ)
    (hδ_pos : 0 < δ) (hR : ‖p‖ ≤ 2)
    (h_near : p ∈ Metric.cthickening δ (ℓ.1 : Set Plane))
    (hv1 : (getDirV ℓ) 1 ≠ 0)
    (h_slope : |(affineLineParams ℓ).1| ≤ 1) :
    |(affineLineParams ℓ).2| ≤ 4 + 2 * δ := by
  let a := (affineLineParams ℓ).1
  let b := (affineLineParams ℓ).2
  have h_p0 : |p 0| ≤ 2 := by
    have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm p 0
    linarith
  have h_p1 : |p 1| ≤ 2 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
    linarith
  have h1 : |b - (p 0 - a * p 1)| ≤ 2 * δ :=
    near_point_intercept_bound_affine hδ_pos h_slope hv1 h_near
  have h_tri : |b| ≤ |b - (p 0 - a * p 1)| + |p 0 - a * p 1| := by
    have h : |b - (0 : ℝ)| ≤ |b - (p 0 - a * p 1)| + |(p 0 - a * p 1) - (0 : ℝ)| :=
      abs_sub_le b (p 0 - a * p 1) 0
    simpa using h
  have h2 : |b| ≤ |p 0 - a * p 1| + 2 * δ := by
    calc |b|
      ≤ |b - (p 0 - a * p 1)| + |p 0 - a * p 1| := h_tri
    _ ≤ 2 * δ + |p 0 - a * p 1| := by gcongr
    _ = |p 0 - a * p 1| + 2 * δ := by ring
  have h3 : |p 0 - a * p 1| ≤ |p 0| + |a| * |p 1| := by
    calc |p 0 - a * p 1|
      ≤ |p 0| + |a * p 1| := by exact abs_sub (p.ofLp 0) (a * p.ofLp 1)
    _ = |p 0| + |a| * |p 1| := by rw [abs_mul]
  have h4 : |p 0| + |a| * |p 1| ≤ 4 := by
    calc |p 0| + |a| * |p 1|
      ≤ 2 + 1 * 2 := by gcongr <;> linarith [abs_le.mp h_slope]
    _ = 4 := by norm_num
  linarith

/-- Bound on intercept difference for two lines near p with ‖p‖ ≤ 2. -/
lemma intercept_diff_bound_R2 (ℓ₁ ℓ₂ : AffineLine) (p : Plane) (δ : ℝ)
    (hδ_pos : 0 < δ) (hR : ‖p‖ ≤ 2)
    (h_near1 : p ∈ Metric.cthickening δ (ℓ₁.1 : Set Plane))
    (h_near2 : p ∈ Metric.cthickening δ (ℓ₂.1 : Set Plane))
    (h1_v1 : (getDirV ℓ₁) 1 ≠ 0) (h2_v1 : (getDirV ℓ₂) 1 ≠ 0)
    (h_slope1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (h_slope2 : |(affineLineParams ℓ₂).1| ≤ 1) :
    |(affineLineParams ℓ₁).2 - (affineLineParams ℓ₂).2| ≤
    4 * δ + 2 * |(affineLineParams ℓ₁).1 - (affineLineParams ℓ₂).1| := by
  set a1 := (affineLineParams ℓ₁).1 with ha1
  set b1 := (affineLineParams ℓ₁).2 with hb1
  set a2 := (affineLineParams ℓ₂).1 with ha2
  set b2 := (affineLineParams ℓ₂).2 with hb2
  have h_p1 : |p 1| ≤ 2 := by
    have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
    linarith
  let x1 := p 0 - a1 * p 1
  let x2 := p 0 - a2 * p 1
  have h1 : |b1 - x1| ≤ 2 * δ :=
    near_point_intercept_bound_affine hδ_pos h_slope1 h1_v1 h_near1
  have h2 : |b2 - x2| ≤ 2 * δ :=
    near_point_intercept_bound_affine hδ_pos h_slope2 h2_v1 h_near2
  have h2' : |x2 - b2| ≤ 2 * δ := by
    have h2'' : |x2 - b2| = |b2 - x2| := by rw [abs_sub_comm]
    rw [h2'']; exact h2
  have h4 : |x1 - x2| = |a1 - a2| * |p 1| := by
    have h5 : x1 - x2 = (a2 - a1) * p 1 := by simp [x1, x2] <;> ring
    rw [h5, abs_mul]
    have h6 : |a2 - a1| = |a1 - a2| := by
      rw [show a2 - a1 = -(a1 - a2) by ring, abs_neg]
    rw [h6] <;> ring
  have h5 : |a1 - a2| * |p 1| ≤ 2 * |a1 - a2| := by
    have h6 : 0 ≤ |a1 - a2| := by positivity
    nlinarith [h_p1]
  have h_main : |b1 - b2| ≤ |b1 - x1| + |x1 - x2| + |x2 - b2| := by
    have h7 : b1 - b2 = (b1 - x1) + (x1 - x2) + (x2 - b2) := by ring
    rw [h7]
    have h8 : |(b1 - x1) + (x1 - x2) + (x2 - b2)| ≤
        |b1 - x1| + |x1 - x2| + |x2 - b2| := by
      calc
        _ ≤ |(b1 - x1) + (x1 - x2)| + |x2 - b2| := by exact abs_add_le (b1 - x1 + (x1 - x2)) (x2 - b2)
      _ ≤ |b1 - x1| + |x1 - x2| + |x2 - b2| := by gcongr; exact abs_add_le (b1 - x1) (x1 - x2)
    exact h8
  rw [h4] at h_main
  linarith [h1, h2', h5]

/-- Combined distance bound for lines near p with ‖p‖ ≤ 2:
    dist(ℓ₁,ℓ₂) ≤ 60·|a₁-a₂| + 20δ. -/
lemma dist_bound_near_point_R2 (ℓ₁ ℓ₂ : AffineLine) (p : Plane) (δ : ℝ)
    (hδ_pos : 0 < δ) (hR : ‖p‖ ≤ 2) (hδ_le_one : δ ≤ 1)
    (h_near1 : p ∈ Metric.cthickening δ (ℓ₁.1 : Set Plane))
    (h_near2 : p ∈ Metric.cthickening δ (ℓ₂.1 : Set Plane))
    (h1_v1 : (getDirV ℓ₁) 1 ≠ 0) (h2_v1 : (getDirV ℓ₂) 1 ≠ 0)
    (h_slope1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (h_slope2 : |(affineLineParams ℓ₂).1| ≤ 1) :
    AffineLine.dist ℓ₁ ℓ₂ ≤ 60 * |(affineLineParams ℓ₁).1 - (affineLineParams ℓ₂).1| + 20 * δ := by
  set a1 := (affineLineParams ℓ₁).1 with ha1
  set b1 := (affineLineParams ℓ₁).2 with hb1
  set a2 := (affineLineParams ℓ₂).1 with ha2
  set b2 := (affineLineParams ℓ₂).2 with hb2
  let d := |a1 - a2|
  have h_d_nonneg : 0 ≤ d := by positivity
  have h_d_le_two : d ≤ 2 := by
    have h3 : |a1 - a2| ≤ |a1| + |a2| := by exact abs_sub a1 a2
    linarith [abs_le.mp h_slope1, abs_le.mp h_slope2]
  have h_dir : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ 3 * d := by
    have h_dir2 : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ 2 * d :=
      direction_proj_upper_bound ℓ₁ ℓ₂ h1_v1 h2_v1
    linarith
  have h_off1 := offset_formula ℓ₁ h1_v1
  have h_off2 := offset_formula ℓ₂ h2_v1
  have h_b2 : |b2| ≤ 4 + 2 * δ :=
    b_bound_R2 ℓ₂ p δ hδ_pos hR h_near2 h2_v1 h_slope2
  have h_off : ‖ℓ₁.offset - ℓ₂.offset‖ ≤ (4 + 2 * δ) * d + |b1 - b2| :=
    offset_diff_bound_tight (a1 := a1) (b1 := b1) (a2 := a2) (b2 := b2) (B := 4 + 2 * δ)
      h_b2 (by positivity) ℓ₁.offset ℓ₂.offset h_off1.1 h_off1.2 h_off2.1 h_off2.2
  have h_b_diff : |b1 - b2| ≤ 4 * δ + 2 * d :=
    intercept_diff_bound_R2 ℓ₁ ℓ₂ p δ hδ_pos hR h_near1 h_near2 h1_v1 h2_v1 h_slope1 h_slope2
  have h_main : AffineLine.dist ℓ₁ ℓ₂ ≤ (9 + 2 * δ) * d + 4 * δ := by
    have h_dist_def : AffineLine.dist ℓ₁ ℓ₂ =
        ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
        ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    rw [h_dist_def]
    calc ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
           ‖ℓ₁.offset - ℓ₂.offset‖
        ≤ 3 * d + ((4 + 2 * δ) * d + |b1 - b2|) := by gcongr
      _ = (7 + 2 * δ) * d + |b1 - b2| := by ring
      _ ≤ (7 + 2 * δ) * d + (4 * δ + 2 * d) := by gcongr
      _ = (9 + 2 * δ) * d + 4 * δ := by ring
  have h_final : (9 + 2 * δ) * d + 4 * δ ≤ 60 * d + 20 * δ := by
    have h1 : (9 + 2 * δ) * d ≤ 60 * d := by
      have h2 : 9 + 2 * δ ≤ 60 := by linarith
      have h3 : 0 ≤ d := by positivity
      nlinarith
    have h4 : 4 * δ ≤ 20 * δ := by linarith
    linarith
  exact h_main.trans h_final

/-- Construct a Plane from two components. -/
def mkPlane (a b : ℝ) : Plane :=
  WithLp.toLp (2 : ENNReal) fun i : Fin 2 => if i = 0 then a else b

lemma mkPlane_apply0 (a b : ℝ) : (mkPlane a b) 0 = a := by
  simp [mkPlane] <;> norm_num

lemma mkPlane_apply1 (a b : ℝ) : (mkPlane a b) 1 = b := by
  simp [mkPlane] <;> norm_num

/-- The affine subspace x = a*y + b. -/
noncomputable def makeAffineSubspace (a b : ℝ) : AffineSubspace ℝ Plane :=
  AffineSubspace.mk' (mkPlane b 0) (Submodule.span ℝ {mkPlane a 1})

/-- Construct an AffineLine with slope a and intercept b. -/
noncomputable def makeAffineLine (a b : ℝ) : AffineLine :=
  let v : Plane := mkPlane a 1
  have h_v_ne_zero : v ≠ 0 := by
    intro h
    have h1 : (v 1) = 0 := by
      have h2 : ∀ (x : Plane), x = 0 → x 1 = 0 := by intro x hx; rw [hx] <;> simp
      exact h2 v h
    simp [v, mkPlane] at h1 <;> norm_num at h1
  have h_finrank : Module.finrank ℝ (makeAffineSubspace a b).direction = 1 := by
    have h_dir : (makeAffineSubspace a b).direction = Submodule.span ℝ {v} := by
      simp [makeAffineSubspace, AffineSubspace.direction_mk'] <;> rfl
    rw [h_dir]
    exact finrank_span_singleton h_v_ne_zero
  ⟨makeAffineSubspace a b, h_finrank⟩

lemma makeAffineLine_direction (a b : ℝ) :
    (makeAffineLine a b).1.direction = Submodule.span ℝ {mkPlane a 1} := by
  have h : (makeAffineLine a b).1 = makeAffineSubspace a b := by
    unfold makeAffineLine <;> simp
  rw [h]
  simp [makeAffineSubspace, AffineSubspace.direction_mk'] <;> rfl

lemma makeAffineLine_v1 (a b : ℝ) : (getDirV (makeAffineLine a b)) 1 ≠ 0 := by
  set ℓ := makeAffineLine a b with hℓ
  set v : Plane := mkPlane a 1 with hv
  have h_dir : ℓ.1.direction = Submodule.span ℝ {v} := makeAffineLine_direction a b
  have h1 : getDirV ℓ ∈ ℓ.1.direction := (getDirV_spec ℓ).1
  rw [h_dir] at h1
  have h2 : ∃ (c : ℝ), c • v = getDirV ℓ := by
    simpa [Submodule.mem_span_singleton] using h1
  rcases h2 with ⟨c, hc⟩
  have hc' : getDirV ℓ = c • v := hc.symm
  have hc_ne_zero : c ≠ 0 := by
    intro h
    have h3 : getDirV ℓ = 0 := by rw [hc', h] <;> simp
    exact (getDirV_spec ℓ).2 h3
  have h4 : (getDirV ℓ) 1 = c := by
    rw [hc']
    simp [v, mkPlane_apply0, mkPlane_apply1, SMul.smul] <;> norm_num
  rw [h4]
  exact hc_ne_zero

lemma makeAffineLine_params (a b : ℝ) :
    affineLineParams (makeAffineLine a b) = (a, b) := by
  set ℓ := makeAffineLine a b with hℓ
  set v : Plane := mkPlane a 1 with hv
  have h_dir : ℓ.1.direction = Submodule.span ℝ {v} := makeAffineLine_direction a b
  have h1 : getDirV ℓ ∈ ℓ.1.direction := (getDirV_spec ℓ).1
  rw [h_dir] at h1
  have h2 : ∃ (c : ℝ), c • v = getDirV ℓ := by
    simpa [Submodule.mem_span_singleton] using h1
  rcases h2 with ⟨c, hc⟩
  have hc' : getDirV ℓ = c • v := hc.symm
  have hc_ne_zero : c ≠ 0 := by
    intro h
    have h3 : getDirV ℓ = 0 := by rw [hc', h] <;> simp
    exact (getDirV_spec ℓ).2 h3
  have hv0 : (getDirV ℓ) 0 = c * a := by
    rw [hc']; simp [v, mkPlane_apply0, mkPlane_apply1, SMul.smul] <;> norm_num
  have hv1 : (getDirV ℓ) 1 = c := by
    rw [hc']; simp [v, mkPlane_apply0, mkPlane_apply1, SMul.smul] <;> norm_num
  have h_slope : (affineLineParams ℓ).1 = a := by
    simp [affineLineParams, hv0, hv1, hc_ne_zero] <;> field_simp <;> ring
  have h_point_in_line : mkPlane b 0 ∈ ℓ.1 := by
    have h_sub : (makeAffineLine a b).1 = makeAffineSubspace a b := by
      unfold makeAffineLine <;> simp
    rw [h_sub, makeAffineSubspace]
    simp [AffineSubspace.mem_mk', mkPlane_apply0, mkPlane_apply1] <;> norm_num
  have h_off_line : ℓ.offset ∈ ℓ.1 := AffineLine.offset_mem ℓ
  have h_vsub : ℓ.offset -ᵥ (mkPlane b 0) ∈ ℓ.1.direction :=
    AffineSubspace.vsub_mem_direction h_off_line h_point_in_line
  rw [h_dir] at h_vsub
  have h'' : ∃ (d : ℝ), d • v = ℓ.offset -ᵥ (mkPlane b 0) := by
    simpa [Submodule.mem_span_singleton] using h_vsub
  rcases h'' with ⟨d, hd⟩
  have hd' : ℓ.offset -ᵥ (mkPlane b 0) = d • v := hd.symm
  have h1 : ℓ.offset 0 - b = d * a := by
    have h_eq : (ℓ.offset -ᵥ (mkPlane b 0)) 0 = (d • v) 0 := by rw [hd']
    simpa [v, mkPlane_apply0, mkPlane_apply1, SMul.smul] using h_eq
  have h2 : ℓ.offset 1 = d := by
    have h_eq : (ℓ.offset -ᵥ (mkPlane b 0)) 1 = (d • v) 1 := by rw [hd']
    simpa [v, mkPlane_apply0, mkPlane_apply1, SMul.smul] using h_eq
  have h_off_eq : ℓ.offset 0 = a * ℓ.offset 1 + b := by
    have h3 : ℓ.offset 0 = b + d * a := by linarith
    rw [h3, h2] <;> ring
  have h_def2 : (affineLineParams ℓ).2 = ℓ.offset 0 - (affineLineParams ℓ).1 * ℓ.offset 1 := by
    simp [affineLineParams] <;> aesop
  have h_intercept : (affineLineParams ℓ).2 = b := by
    rw [h_def2, h_slope, h_off_eq] <;> ring
  exact Prod.ext h_slope h_intercept

/-- Given x ∈ [lo, hi], find k ∈ {0,...,n} with |x - (lo + k·step)| ≤ step/2,
    where step = (hi-lo)/n. -/
lemma real_grid_cover (x lo hi : ℝ) (n : ℕ) (hn_pos : 0 < n)
    (hlo : lo ≤ x) (hhi : x ≤ hi) :
    ∃ (k : ℕ), k ≤ n ∧ |x - (lo + (k : ℝ) * ((hi - lo) / (n : ℝ)))| ≤ ((hi - lo) / (n : ℝ)) / 2 := by
  have h_le : lo ≤ hi := by linarith
  by_cases h_eq : hi = lo
  · have h_x_eq : x = hi := by linarith
    have h_diff : hi - lo = 0 := by linarith
    refine ⟨0, by linarith, ?_⟩
    have h9 : (hi - lo) / (n : ℝ) = 0 := by
      rw [h_diff] <;> simp
    have h10 : x = lo := by linarith
    rw [h9, h10]
    <;> simp
  · have h_lt : lo < hi := by
      exact lt_of_le_of_ne h_le (Ne.symm h_eq)
    have h_diff_pos : 0 < hi - lo := by linarith
    set step : ℝ := (hi - lo) / (n : ℝ) with hstep_def
    have hstep_pos : 0 < step := by positivity
    set y : ℝ := (x - lo) / step with hy_def
    have hy_nonneg : 0 ≤ y := by
      rw [hy_def]; apply div_nonneg <;> linarith
    have hy_le : y ≤ (n : ℝ) := by
      rw [hy_def, hstep_def]
      have h' : 0 < (hi - lo) / (n : ℝ) := by positivity
      have h9 : (x - lo) ≤ (n : ℝ) * ((hi - lo) / (n : ℝ)) := by
        have h10 : (n : ℝ) * ((hi - lo) / (n : ℝ)) = hi - lo := by
          field_simp [h'.ne'] <;> ring
        rw [h10] <;> linarith
      have h : (x - lo) / ((hi - lo) / (n : ℝ)) ≤ (n : ℝ) := by
        calc (x - lo) / ((hi - lo) / (n : ℝ))
            ≤ ((n : ℝ) * ((hi - lo) / (n : ℝ))) / ((hi - lo) / (n : ℝ)) := by gcongr
          _ = (n : ℝ) := by field_simp [h'.ne'] <;> ring
      exact h
    let k : ℤ := Int.floor (y + 1 / 2)
    have hk1 : (k : ℝ) ≤ y + 1 / 2 := Int.floor_le (y + 1 / 2)
    have hk2 : y + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one (y + 1 / 2)
    have h_abs : |y - (k : ℝ)| ≤ 1 / 2 := by
      have h1 : y - (k : ℝ) ≤ 1 / 2 := by linarith
      have h2 : -(1 / 2 : ℝ) ≤ y - (k : ℝ) := by linarith
      exact abs_le.mpr ⟨h2, h1⟩
    have hk_nonneg : 0 ≤ k := by
      have h_pos : 0 < y + 1 / 2 := by linarith
      exact Int.floor_nonneg.mpr (by linarith)
    have hk_le_n : k ≤ (n : ℤ) := by
      have h_lt : (k : ℝ) < (n : ℝ) + 1 := by linarith
      have h : k ≤ (n : ℤ) := by
        by_contra h'
        have h'' : k ≥ (n : ℤ) + 1 := by linarith
        have h''' : (k : ℝ) ≥ (n : ℝ) + 1 := by exact_mod_cast h''
        linarith
      exact h
    let k_nat : ℕ := k.toNat
    have hk_nat_eq : (k_nat : ℝ) = (k : ℝ) := by
      have h : k_nat = k := Int.toNat_of_nonneg hk_nonneg
      norm_cast <;> simpa using h
    have hk_nat_le : k_nat ≤ n := by
      have h : (k_nat : ℤ) = k := by
        simp [k_nat, Int.toNat_of_nonneg hk_nonneg]
      omega
    refine ⟨k_nat, hk_nat_le, ?_⟩
    have h_x_eq : x - lo = y * step := by
      rw [hy_def] <;> field_simp [hstep_pos.ne'] <;> ring
    have h_factor : y * step - (k_nat : ℝ) * step = step * (y - (k_nat : ℝ)) := by ring
    calc |x - (lo + (k_nat : ℝ) * step)|
        = |(x - lo) - (k_nat : ℝ) * step| := by ring_nf
      _ = |y * step - (k_nat : ℝ) * step| := by rw [h_x_eq]
      _ = |step * (y - (k_nat : ℝ))| := by rw [h_factor]
      _ = |step| * |y - (k_nat : ℝ)| := by rw [abs_mul]
      _ = step * |y - (k_nat : ℝ)| := by
        have h_step_abs : |step| = step := abs_of_pos hstep_pos
        rw [h_step_abs] <;> ring
      _ = step * |y - (k : ℝ)| := by rw [hk_nat_eq]
      _ ≤ step * (1 / 2 : ℝ) := by gcongr
      _ = step / 2 := by ring

-- ============================================================================
-- Distance bound for lines near a point
-- ============================================================================

/-- Distance bound: dist(ℓ₁,ℓ₂) ≤ (2+B)|a₁-a₂| + |b₁-b₂| when |b₂| ≤ B. -/
lemma dist_bound_general (ℓ₁ ℓ₂ : AffineLine)
    (h1_v1 : (getDirV ℓ₁) 1 ≠ 0)
    (h2_v1 : (getDirV ℓ₂) 1 ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) (hb2 : |(affineLineParams ℓ₂).2| ≤ B) :
    AffineLine.dist ℓ₁ ℓ₂ ≤ (2 + B) * |(affineLineParams ℓ₁).1 - (affineLineParams ℓ₂).1| +
      |(affineLineParams ℓ₁).2 - (affineLineParams ℓ₂).2| := by
  let a1 := (affineLineParams ℓ₁).1
  let b1 := (affineLineParams ℓ₁).2
  let a2 := (affineLineParams ℓ₂).1
  let b2 := (affineLineParams ℓ₂).2
  have h_off1 : ℓ₁.offset 0 = b1 / (1 + a1^2) := (offset_formula ℓ₁ h1_v1).1
  have h_off1' : ℓ₁.offset 1 = -a1 * b1 / (1 + a1^2) := (offset_formula ℓ₁ h1_v1).2
  have h_off2 : ℓ₂.offset 0 = b2 / (1 + a2^2) := (offset_formula ℓ₂ h2_v1).1
  have h_off2' : ℓ₂.offset 1 = -a2 * b2 / (1 + a2^2) := (offset_formula ℓ₂ h2_v1).2
  have h_dir_bound : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ 2 * |a1 - a2| :=
    direction_proj_upper_bound ℓ₁ ℓ₂ h1_v1 h2_v1
  have h_off_bound : ‖ℓ₁.offset - ℓ₂.offset‖ ≤ B * |a1 - a2| + |b1 - b2| :=
    offset_diff_bound_tight hb2 hB ℓ₁.offset ℓ₂.offset h_off1 h_off1' h_off2 h_off2'
  have h_main : AffineLine.dist ℓ₁ ℓ₂ =
      ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ + ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
  rw [h_main]
  linarith

-- ============================================================================
-- Main strip_covering theorem
-- ============================================================================

/-- Strip covering: a slope strip of width 2δ near p can be covered by ≤500 δ-balls. -/
lemma strip_covering (p : Plane) (δ : ℝ) (hδ_pos : 0 < δ)
    (hp : p ∈ Metric.closedBall 0 1) (hδ_le_one : δ ≤ 1)
    (T : Set AffineLine)
    (h_near : ∀ ℓ ∈ T, p ∈ Metric.cthickening δ ℓ.1)
    (h_slope : ∀ ℓ ∈ T, |(affineLineParams ℓ).1| ≤ 1)
    (h_v1 : ∀ ℓ ∈ T, (getDirV ℓ) 1 ≠ 0)
    (a_center : ℝ) :
    ∃ (C : Finset AffineLine),
      Metric.IsCover δ.toNNReal
        (T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ}) C ∧
      C.card ≤ 500 := by
  set S : Set AffineLine := T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ} with hS_def
  by_cases hS : S.Nonempty
  · rcases hS with ⟨ℓ0, hℓ0⟩
    have hℓ0_T : ℓ0 ∈ T := hℓ0.1
    have hℓ0_strip : |(affineLineParams ℓ0).1 - a_center| ≤ δ := hℓ0.2
    let a0 := (affineLineParams ℓ0).1
    have ha0_slope : |a0| ≤ 1 := h_slope ℓ0 hℓ0_T
    have ha_center_bound : |a_center| ≤ 1 + δ := by
      have h_eq : a_center = a0 + (a_center - a0) := by ring
      rw [h_eq]
      have h1 : |a0 + (a_center - a0)| ≤ |a0| + |a_center - a0| := by exact abs_add_le a0 (a_center - a0)
      have h2 : |a_center - a0| = |a0 - a_center| := by
        rw [show a_center - a0 = -(a0 - a_center) by ring]
        rw [abs_neg]
      rw [h2] at h1
      linarith
    have h_p0 : |p 0| ≤ 1 := by
      have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm p 0
      have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
      linarith
    have h_p1 : |p 1| ≤ 1 := by
      have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
      have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp
      linarith
    let b_center : ℝ := p 0 - a_center * p 1
    have hb_center_bound : |b_center| ≤ 2 + δ := by
      have h1 : |b_center| ≤ |p 0| + |a_center * p 1| := by
        have h2 : b_center = p 0 - a_center * p 1 := by rfl
        rw [h2]
        exact abs_sub (p.ofLp 0) (a_center * p.ofLp 1)
      have h3 : |a_center * p 1| = |a_center| * |p 1| := by rw [abs_mul]
      rw [h3] at h1
      calc |b_center| ≤ |p 0| + |a_center| * |p 1| := h1
        _ ≤ 1 + (1 + δ) * 1 := by gcongr <;> linarith
        _ = 2 + δ := by ring
    let step_a : ℝ := δ / 16
    let step_b : ℝ := δ / 2
    let I_a : Finset ℕ := Finset.range 33
    let I_b : Finset ℕ := Finset.range 13
    let a_grid (k : ℕ) : ℝ := a_center - δ + (k : ℝ) * step_a
    let b_grid (j : ℕ) : ℝ := b_center - 3 * δ + (j : ℝ) * step_b
    classical
    let C : Finset AffineLine :=
      (I_a ×ˢ I_b).image (fun p : ℕ × ℕ => makeAffineLine (a_grid p.1) (b_grid p.2))
    have hC_card : C.card ≤ 500 := by
      have h1 : C.card ≤ (I_a ×ˢ I_b).card := by
        exact Finset.card_image_le
      have h2 : (I_a ×ˢ I_b).card = 33 * 13 := by
        simp [I_a, I_b, Finset.card_product] <;> norm_num
      rw [h2] at h1
      have h3 : C.card ≤ 429 := h1
      linarith
    have h_cover : Metric.IsCover δ.toNNReal S C := by
      intro ℓ hℓ
      have hℓ_T : ℓ ∈ T := hℓ.1
      have hℓ_strip : |(affineLineParams ℓ).1 - a_center| ≤ δ := hℓ.2
      let a := (affineLineParams ℓ).1
      let b := (affineLineParams ℓ).2
      have ha_slope : |a| ≤ 1 := h_slope ℓ hℓ_T
      have hv1 : (getDirV ℓ) 1 ≠ 0 := h_v1 ℓ hℓ_T
      have ha_lo : a_center - δ ≤ a := by linarith [abs_le.mp hℓ_strip]
      have ha_hi : a ≤ a_center + δ := by linarith [abs_le.mp hℓ_strip]
      have h_b_near : |b - (p 0 - a * p 1)| ≤ 2 * δ :=
        near_point_intercept_bound_affine hδ_pos ha_slope hv1 (h_near ℓ hℓ_T)
      have h_diff_eq : (p 0 - a * p 1) - b_center = (a_center - a) * p 1 := by
        simp [b_center] <;> ring
      have h2 : |(p 0 - a * p 1) - b_center| = |a_center - a| * |p 1| := by
        rw [h_diff_eq, abs_mul]
      have hb_bound : |b - b_center| ≤ 3 * δ := by
        have h1 : |b - b_center| ≤ |b - (p 0 - a * p 1)| + |(p 0 - a * p 1) - b_center| := by exact abs_sub_le b (p.ofLp 0 - a * p.ofLp 1) b_center
        have h3 : |a_center - a| ≤ δ := by simpa [abs_sub_comm] using hℓ_strip
        have h4 : |p 1| ≤ 1 := h_p1
        calc |b - b_center|
            ≤ |b - (p 0 - a * p 1)| + |(p 0 - a * p 1) - b_center| := h1
          _ = |b - (p 0 - a * p 1)| + |a_center - a| * |p 1| := by rw [h2]
          _ ≤ 2 * δ + δ * 1 := by gcongr
          _ = 3 * δ := by ring
      have hb_lo : b_center - 3 * δ ≤ b := by linarith [abs_le.mp hb_bound]
      have hb_hi : b ≤ b_center + 3 * δ := by linarith [abs_le.mp hb_bound]
      rcases real_grid_cover a (a_center - δ) (a_center + δ) 32 (by norm_num) ha_lo ha_hi with ⟨k, hk_le, hk_cover⟩
      rcases real_grid_cover b (b_center - 3 * δ) (b_center + 3 * δ) 12 (by norm_num) hb_lo hb_hi with ⟨j, hj_le, hj_cover⟩
      have hk_in : k ∈ I_a := by
        simp [I_a, hk_le] <;> omega
      have hj_in : j ∈ I_b := by
        simp [I_b, hj_le] <;> omega
      have h_step_a_eq : (a_center + δ - (a_center - δ)) / (32 : ℝ) = step_a := by
        simp [step_a] <;> ring
      have h_step_b_eq : (b_center + 3 * δ - (b_center - 3 * δ)) / (12 : ℝ) = step_b := by
        simp [step_b] <;> ring
      have hk_cover' : |a - a_grid k| ≤ step_a / 2 := by
        have h_step : (a_center + δ - (a_center - δ)) / (↑32 : ℝ) = step_a := by
          exact_mod_cast h_step_a_eq
        have h_goal : a_center - δ + (k : ℝ) * step_a = a_grid k := by
          simp [a_grid] <;> ring
        have h_main : |a - (a_center - δ + (k : ℝ) * ((a_center + δ - (a_center - δ)) / (↑32 : ℝ)))| ≤
            ((a_center + δ - (a_center - δ)) / (↑32 : ℝ)) / 2 := hk_cover
        rw [h_step] at h_main
        rw [h_goal] at h_main
        exact h_main
      have hj_cover' : |b - b_grid j| ≤ step_b / 2 := by
        have h_step : (b_center + 3 * δ - (b_center - 3 * δ)) / (↑12 : ℝ) = step_b := by
          exact_mod_cast h_step_b_eq
        have h_goal : b_center - 3 * δ + (j : ℝ) * step_b = b_grid j := by
          simp [b_grid] <;> ring
        have h_main : |b - (b_center - 3 * δ + (j : ℝ) * ((b_center + 3 * δ - (b_center - 3 * δ)) / (↑12 : ℝ)))| ≤
            ((b_center + 3 * δ - (b_center - 3 * δ)) / (↑12 : ℝ)) / 2 := hj_cover
        rw [h_step] at h_main
        rw [h_goal] at h_main
        exact h_main
      let ℓ_g := makeAffineLine (a_grid k) (b_grid j)
      have hℓg_in_C : ℓ_g ∈ C := by
        apply Finset.mem_image.mpr
        refine ⟨(k, j), ?_, rfl⟩
        exact Finset.mem_product.mpr ⟨hk_in, hj_in⟩
      have hℓg_v1 : (getDirV ℓ_g) 1 ≠ 0 := makeAffineLine_v1 (a_grid k) (b_grid j)
      have hℓg_params : affineLineParams ℓ_g = (a_grid k, b_grid j) :=
        makeAffineLine_params (a_grid k) (b_grid j)
      have hbg_bound : |b_grid j| ≤ 6 := by
        have h_j_le : (j : ℝ) ≤ 12 := by exact_mod_cast hj_le
        have h_j_nonneg : 0 ≤ (j : ℝ) := by positivity
        have h1 : b_grid j - b_center = (j : ℝ) * step_b - 3 * δ := by
          simp [b_grid] <;> ring
        have h2 : |b_grid j - b_center| ≤ 3 * δ := by
          rw [h1]
          have h3 : (j : ℝ) * step_b - 3 * δ = δ * ((j : ℝ) / 2 - 3) := by
            simp [step_b] <;> ring
          rw [h3]
          have h4 : |(j : ℝ) / 2 - 3| ≤ 3 := by
            have h5 : -3 ≤ (j : ℝ) / 2 - 3 := by linarith
            have h6 : (j : ℝ) / 2 - 3 ≤ 3 := by linarith
            exact abs_le.mpr ⟨h5, h6⟩
          calc |δ * ((j : ℝ) / 2 - 3)| = |δ| * |(j : ℝ) / 2 - 3| := by rw [abs_mul]
            _ = δ * |(j : ℝ) / 2 - 3| := by rw [abs_of_pos hδ_pos]
            _ ≤ δ * 3 := by gcongr
            _ = 3 * δ := by ring
        have h4 : |b_center| ≤ 3 := by
          calc |b_center| ≤ 2 + δ := hb_center_bound
            _ ≤ 3 := by linarith [hδ_le_one]
        have h5 : b_grid j = b_center + (b_grid j - b_center) := by ring
        rw [h5]
        have h6 : |b_center + (b_grid j - b_center)| ≤ |b_center| + |b_grid j - b_center| := by
          simpa [Real.norm_eq_abs] using norm_add_le b_center (b_grid j - b_center)
        have h7 : |b_center| + |b_grid j - b_center| ≤ 3 + 3 * δ := by linarith
        have h8 : 3 + 3 * δ ≤ 6 := by linarith [hδ_le_one]
        linarith
      have hbg_bound' : |(affineLineParams ℓ_g).2| ≤ 6 := by
        rw [hℓg_params]
        <;> simpa using hbg_bound
      have h_dist : AffineLine.dist ℓ ℓ_g ≤ δ := by
        have h_bound := dist_bound_general ℓ ℓ_g hv1 hℓg_v1 (B := 6) (by norm_num) hbg_bound'
        rw [hℓg_params] at h_bound
        have h1 : |a - a_grid k| ≤ δ / 32 := by
          have h2 : step_a / 2 = δ / 32 := by simp [step_a] <;> ring
          rw [h2] at hk_cover'
          exact hk_cover'
        have h3 : |b - b_grid j| ≤ δ / 4 := by
          have h4 : step_b / 2 = δ / 4 := by simp [step_b] <;> ring
          rw [h4] at hj_cover'
          exact hj_cover'
        linarith
      have h_edist : edist ℓ ℓ_g ≤ ↑(δ.toNNReal) := by
        have h5 : edist ℓ ℓ_g = ENNReal.ofReal (dist ℓ ℓ_g) := edist_dist ℓ ℓ_g
        rw [h5]
        have h6 : (↑(δ.toNNReal) : ENNReal) = ENNReal.ofReal δ := by
          have h7 : 0 ≤ δ := by linarith
          have h8 : (δ.toNNReal : ℝ) = δ := by
            exact Real.coe_toNNReal δ h7
          have h9 : (↑(δ.toNNReal) : ENNReal) = ENNReal.ofReal (δ.toNNReal : ℝ) := by
            exact Eq.symm ENNReal.ofReal_coe_nnreal
          rw [h9, h8]
        rw [h6]
        exact ENNReal.ofReal_le_ofReal h_dist
      exact ⟨ℓ_g, hℓg_in_C, h_edist⟩
    have h_cover' : Metric.IsCover δ.toNNReal (T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ}) C := by
      rw [←hS_def]
      exact h_cover
    exact ⟨C, h_cover', hC_card⟩
  · -- Empty strip: empty cover works
    have hS_empty : S = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hS
    have h_cover : Metric.IsCover δ.toNNReal S (∅ : Finset AffineLine) := by
      rw [hS_empty]
      intro x hx
      simpa using hx
    have h_cover' : Metric.IsCover δ.toNNReal (T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ}) (∅ : Finset AffineLine) := by
      rw [←hS_def]
      exact h_cover
    exact ⟨(∅ : Finset AffineLine), h_cover', by simp⟩

/-- Generalized strip covering: works for `‖p‖ ≤ 2` instead of `p ∈ closedBall 0 1`.
    Covers a slope strip by ≤600 δ-balls. -/
lemma strip_covering_R2 (p : Plane) (δ : ℝ) (hδ_pos : 0 < δ)
    (hR : ‖p‖ ≤ 2) (hδ_le_one : δ ≤ 1)
    (T : Set AffineLine)
    (h_near : ∀ ℓ ∈ T, p ∈ Metric.cthickening δ ℓ.1)
    (h_slope : ∀ ℓ ∈ T, |(affineLineParams ℓ).1| ≤ 1)
    (h_v1 : ∀ ℓ ∈ T, (getDirV ℓ) 1 ≠ 0)
    (a_center : ℝ) :
    ∃ (C : Finset AffineLine),
      Metric.IsCover δ.toNNReal
        (T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ}) C ∧
      C.card ≤ 600 := by
  set S : Set AffineLine := T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ} with hS_def
  by_cases hS : S.Nonempty
  · rcases hS with ⟨ℓ0, hℓ0⟩
    have hℓ0_T : ℓ0 ∈ T := hℓ0.1
    have hℓ0_strip : |(affineLineParams ℓ0).1 - a_center| ≤ δ := hℓ0.2
    let a0 := (affineLineParams ℓ0).1
    have ha0_slope : |a0| ≤ 1 := h_slope ℓ0 hℓ0_T
    have ha_center_bound : |a_center| ≤ 1 + δ := by
      have h_eq : a_center = a0 + (a_center - a0) := by ring
      rw [h_eq]
      have h1 : |a0 + (a_center - a0)| ≤ |a0| + |a_center - a0| := by exact abs_add_le a0 (a_center - a0)
      have h2 : |a_center - a0| = |a0 - a_center| := by
        rw [show a_center - a0 = -(a0 - a_center) by ring]
        rw [abs_neg]
      rw [h2] at h1
      linarith
    have h_p0 : |p 0| ≤ 2 := by
      have h : |p 0| ≤ ‖p‖ := coord_abs_le_norm p 0
      linarith [hR]
    have h_p1 : |p 1| ≤ 2 := by
      have h : |p 1| ≤ ‖p‖ := coord_abs_le_norm p 1
      linarith [hR]
    let b_center : ℝ := p 0 - a_center * p 1
    have hb_center_bound : |b_center| ≤ 2 + (1 + δ) * 2 := by
      have h1 : |b_center| ≤ |p 0| + |a_center * p 1| := by
        have h2 : b_center = p 0 - a_center * p 1 := by rfl
        rw [h2]; exact abs_sub (p.ofLp 0) (a_center * p.ofLp 1)
      have h3 : |a_center * p 1| = |a_center| * |p 1| := by rw [abs_mul]
      rw [h3] at h1
      calc |b_center| ≤ |p 0| + |a_center| * |p 1| := h1
        _ ≤ 2 + (1 + δ) * 2 := by gcongr <;> linarith
    let step_a : ℝ := δ / 16
    let step_b : ℝ := δ / 2
    let I_a : Finset ℕ := Finset.range 33
    let I_b : Finset ℕ := Finset.range 17
    let a_grid (k : ℕ) : ℝ := a_center - δ + (k : ℝ) * step_a
    let b_grid (j : ℕ) : ℝ := b_center - 4 * δ + (j : ℝ) * step_b
    classical
    let C : Finset AffineLine :=
      (I_a ×ˢ I_b).image (fun p : ℕ × ℕ => makeAffineLine (a_grid p.1) (b_grid p.2))
    have hC_card : C.card ≤ 600 := by
      have h1 : C.card ≤ (I_a ×ˢ I_b).card := by exact Finset.card_image_le
      have h2 : (I_a ×ˢ I_b).card = 33 * 17 := by
        simp [I_a, I_b, Finset.card_product] <;> norm_num
      rw [h2] at h1
      have h3 : C.card ≤ 561 := h1
      linarith
    have h_cover : Metric.IsCover δ.toNNReal S C := by
      intro ℓ hℓ
      have hℓ_T : ℓ ∈ T := hℓ.1
      have hℓ_strip : |(affineLineParams ℓ).1 - a_center| ≤ δ := hℓ.2
      let a := (affineLineParams ℓ).1
      let b := (affineLineParams ℓ).2
      have ha_slope : |a| ≤ 1 := h_slope ℓ hℓ_T
      have hv1 : (getDirV ℓ) 1 ≠ 0 := h_v1 ℓ hℓ_T
      have ha_lo : a_center - δ ≤ a := by linarith [abs_le.mp hℓ_strip]
      have ha_hi : a ≤ a_center + δ := by linarith [abs_le.mp hℓ_strip]
      have h_b_near : |b - (p 0 - a * p 1)| ≤ 2 * δ :=
        near_point_intercept_bound_affine hδ_pos ha_slope hv1 (h_near ℓ hℓ_T)
      have h_diff_eq : (p 0 - a * p 1) - b_center = (a_center - a) * p 1 := by
        simp [b_center] <;> ring
      have h2 : |(p 0 - a * p 1) - b_center| = |a_center - a| * |p 1| := by
        rw [h_diff_eq, abs_mul]
      have hb_bound : |b - b_center| ≤ 4 * δ := by
        have h1 : |b - b_center| ≤ |b - (p 0 - a * p 1)| + |(p 0 - a * p 1) - b_center| := by exact abs_sub_le b (p.ofLp 0 - a * p.ofLp 1) b_center
        have h3 : |a_center - a| ≤ δ := by simpa [abs_sub_comm] using hℓ_strip
        have h4 : |p 1| ≤ 2 := h_p1
        calc |b - b_center|
            ≤ |b - (p 0 - a * p 1)| + |(p 0 - a * p 1) - b_center| := h1
          _ = |b - (p 0 - a * p 1)| + |a_center - a| * |p 1| := by rw [h2]
          _ ≤ 2 * δ + δ * 2 := by gcongr
          _ = 4 * δ := by ring
      have hb_lo : b_center - 4 * δ ≤ b := by linarith [abs_le.mp hb_bound]
      have hb_hi : b ≤ b_center + 4 * δ := by linarith [abs_le.mp hb_bound]
      rcases real_grid_cover a (a_center - δ) (a_center + δ) 32 (by norm_num) ha_lo ha_hi with ⟨k, hk_le, hk_cover⟩
      rcases real_grid_cover b (b_center - 4 * δ) (b_center + 4 * δ) 16 (by norm_num) hb_lo hb_hi with ⟨j, hj_le, hj_cover⟩
      have hk_in : k ∈ I_a := by
        simp [I_a, hk_le] <;> omega
      have hj_in : j ∈ I_b := by
        simp [I_b, hj_le] <;> omega
      have hk_cover' : |a - a_grid k| ≤ step_a / 2 := by
        have h_step : (a_center + δ - (a_center - δ)) / (↑32 : ℝ) = step_a := by
          simp [step_a] <;> ring
        have h_goal : a_center - δ + (k : ℝ) * step_a = a_grid k := by
          simp [a_grid] <;> ring
        have h_main : |a - (a_center - δ + (k : ℝ) * ((a_center + δ - (a_center - δ)) / (↑32 : ℝ)))| ≤
            ((a_center + δ - (a_center - δ)) / (↑32 : ℝ)) / 2 := hk_cover
        rw [h_step] at h_main
        rw [h_goal] at h_main
        exact h_main
      have hj_cover' : |b - b_grid j| ≤ step_b / 2 := by
        have h_step : (b_center + 4 * δ - (b_center - 4 * δ)) / (↑16 : ℝ) = step_b := by
          simp [step_b] <;> ring
        have h_goal : b_center - 4 * δ + (j : ℝ) * step_b = b_grid j := by
          simp [b_grid] <;> ring
        have h_main : |b - (b_center - 4 * δ + (j : ℝ) * ((b_center + 4 * δ - (b_center - 4 * δ)) / (↑16 : ℝ)))| ≤
            ((b_center + 4 * δ - (b_center - 4 * δ)) / (↑16 : ℝ)) / 2 := hj_cover
        rw [h_step] at h_main
        rw [h_goal] at h_main
        exact h_main
      let ℓ_g := makeAffineLine (a_grid k) (b_grid j)
      have hℓg_in_C : ℓ_g ∈ C := by
        apply Finset.mem_image.mpr
        refine ⟨(k, j), ?_, rfl⟩
        exact Finset.mem_product.mpr ⟨hk_in, hj_in⟩
      have hℓg_v1 : (getDirV ℓ_g) 1 ≠ 0 := makeAffineLine_v1 (a_grid k) (b_grid j)
      have hℓg_params : affineLineParams ℓ_g = (a_grid k, b_grid j) :=
        makeAffineLine_params (a_grid k) (b_grid j)
      have hbg_bound : |b_grid j| ≤ 10 := by
        have h_j_le : (j : ℝ) ≤ 16 := by exact_mod_cast hj_le
        have h_j_nonneg : 0 ≤ (j : ℝ) := by positivity
        have h1 : b_grid j - b_center = (j : ℝ) * step_b - 4 * δ := by
          simp [b_grid] <;> ring
        have h2 : |b_grid j - b_center| ≤ 4 * δ := by
          rw [h1]
          have h3 : (j : ℝ) * step_b - 4 * δ = δ * ((j : ℝ) / 2 - 4) := by
            simp [step_b] <;> ring
          rw [h3]
          have h4 : |(j : ℝ) / 2 - 4| ≤ 4 := by
            have h5 : -4 ≤ (j : ℝ) / 2 - 4 := by linarith
            have h6 : (j : ℝ) / 2 - 4 ≤ 4 := by linarith
            exact abs_le.mpr ⟨h5, h6⟩
          calc |δ * ((j : ℝ) / 2 - 4)| = |δ| * |(j : ℝ) / 2 - 4| := by rw [abs_mul]
            _ = δ * |(j : ℝ) / 2 - 4| := by rw [abs_of_pos hδ_pos]
            _ ≤ δ * 4 := by gcongr
            _ = 4 * δ := by ring
        have h4 : |b_center| ≤ 4 + 2 * δ := by
          have h4' : |b_center| ≤ 2 + (1 + δ) * 2 := hb_center_bound
          have h_eq : 2 + (1 + δ) * 2 = 4 + 2 * δ := by ring
          rw [h_eq] at h4'
          exact h4'
        have h5 : b_grid j = b_center + (b_grid j - b_center) := by ring
        rw [h5]
        have h6 : |b_center + (b_grid j - b_center)| ≤ |b_center| + |b_grid j - b_center| := by
          simpa [Real.norm_eq_abs] using norm_add_le b_center (b_grid j - b_center)
        have h7 : |b_center| + |b_grid j - b_center| ≤ (4 + 2 * δ) + 4 * δ := by linarith
        have h8 : (4 + 2 * δ) + 4 * δ ≤ 10 := by linarith [hδ_le_one]
        linarith
      have hbg_bound' : |(affineLineParams ℓ_g).2| ≤ 10 := by
        rw [hℓg_params] <;> simpa using hbg_bound
      have h_dist : AffineLine.dist ℓ ℓ_g ≤ δ := by
        have h_bound := dist_bound_general ℓ ℓ_g hv1 hℓg_v1 (B := 10) (by norm_num) hbg_bound'
        rw [hℓg_params] at h_bound
        have h1 : |a - a_grid k| ≤ δ / 32 := by
          have h2 : step_a / 2 = δ / 32 := by simp [step_a] <;> ring
          rw [h2] at hk_cover'
          exact hk_cover'
        have h3 : |b - b_grid j| ≤ δ / 4 := by
          have h4 : step_b / 2 = δ / 4 := by simp [step_b] <;> ring
          rw [h4] at hj_cover'
          exact hj_cover'
        linarith
      have h_edist : edist ℓ ℓ_g ≤ ↑(δ.toNNReal) := by
        have h5 : edist ℓ ℓ_g = ENNReal.ofReal (dist ℓ ℓ_g) := edist_dist ℓ ℓ_g
        rw [h5]
        have h6 : (↑(δ.toNNReal) : ENNReal) = ENNReal.ofReal δ := by
          have h7 : 0 ≤ δ := by linarith
          have h8 : (δ.toNNReal : ℝ) = δ := by exact Real.coe_toNNReal δ h7
          have h9 : (↑(δ.toNNReal) : ENNReal) = ENNReal.ofReal (δ.toNNReal : ℝ) := by exact Eq.symm ENNReal.ofReal_coe_nnreal
          rw [h9, h8]
        rw [h6]
        exact ENNReal.ofReal_le_ofReal h_dist
      exact ⟨ℓ_g, hℓg_in_C, h_edist⟩
    have h_cover' : Metric.IsCover δ.toNNReal (T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ}) C := by
      rw [←hS_def]
      exact h_cover
    exact ⟨C, h_cover', hC_card⟩
  · have hS_empty : S = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using hS
    have h_cover : Metric.IsCover δ.toNNReal S (∅ : Finset AffineLine) := by
      rw [hS_empty]
      intro x hx
      simpa using hx
    have h_cover' : Metric.IsCover δ.toNNReal (T ∩ {ℓ | |(affineLineParams ℓ).1 - a_center| ≤ δ}) (∅ : Finset AffineLine) := by
      rw [←hS_def]
      exact h_cover
    exact ⟨(∅ : Finset AffineLine), h_cover', by simp⟩

/-- Convert `edist x y ≤ ↑d` to `dist x y ≤ (d : ℝ)`. -/
lemma edist_le_to_dist_le {X : Type*} [PseudoMetricSpace X] {x y : X} {d : NNReal}
    (h : edist x y ≤ ↑d) : dist x y ≤ (d : ℝ) := by
  have h_eq : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
  rw [h_eq] at h
  have h_coe : (↑d : ENNReal) = ENNReal.ofReal (d : ℝ) := by simp
  rw [h_coe] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Convert `dist x y ≤ (d : ℝ)` to `edist x y ≤ ↑d` for `d : NNReal`. -/
lemma dist_le_to_edist_le {X : Type*} [PseudoMetricSpace X] {x y : X} {d : NNReal}
    (h : dist x y ≤ (d : ℝ)) : edist x y ≤ ↑d := by
  have h_eq : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
  rw [h_eq]
  have h_coe : (↑d : ENNReal) = ENNReal.ofReal (d : ℝ) := by simp
  rw [h_coe]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h

/-- Covering doubling in ℝ: covering_δ(S) ≤ 2·covering_{2δ}(S). -/
lemma real_covering_doubling {S : Set ℝ} {δ : NNReal} (hδ : 0 < δ) :
    Metric.externalCoveringNumber δ S ≤ 2 * Metric.externalCoveringNumber (2 * δ) S := by
  by_cases h_top : Metric.externalCoveringNumber (2 * δ) S = ⊤
  · rw [h_top] <;> simp
  · have hfin : Metric.externalCoveringNumber (2 * δ) S < ⊤ := lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq hfin with ⟨C, hC, hC_eq⟩
    classical
    let D : Set ℝ := (fun x : ℝ => x - (δ : ℝ)) '' C ∪ (fun x : ℝ => x + (δ : ℝ)) '' C
    have hD_cover : Metric.IsCover δ S D := by
      intro x hx
      have hC' : ∃ (c : ℝ), c ∈ C ∧ (x, c) ∈ {(p : ℝ × ℝ) | edist p.1 p.2 ≤ ↑(2 * δ)} := hC hx
      rcases hC' with ⟨c, hc, hedistance⟩
      have h_edist : edist x c ≤ ↑(2 * δ) := by simpa using hedistance
      have hdist : dist x c ≤ (2 * δ : ℝ) := edist_le_to_dist_le h_edist
      have h_ineq : |x - c| ≤ 2 * (δ : ℝ) := by simpa [dist_eq_norm] using hdist
      by_cases h : x ≤ c
      · have h1 : c - (δ : ℝ) ∈ D := Or.inl ⟨c, hc, by ring⟩
        have h2 : |x - (c - (δ : ℝ))| ≤ (δ : ℝ) := by
          have h3 : c - x ≤ 2 * (δ : ℝ) := by
            have h4 : |x - c| ≤ 2 * (δ : ℝ) := h_ineq
            have h5 : c - x = |x - c| := by
              rw [abs_of_nonpos (show x - c ≤ 0 by linarith)] <;> linarith
            linarith
          have h6 : x - (c - (δ : ℝ)) = (δ : ℝ) - (c - x) := by ring
          rw [h6]
          rw [abs_le] <;> constructor <;> linarith
        have h7 : dist x (c - (δ : ℝ)) ≤ (δ : ℝ) := by simpa [dist_eq_norm] using h2
        have h8 : edist x (c - (δ : ℝ)) ≤ ↑δ := dist_le_to_edist_le h7
        exact ⟨c - (δ : ℝ), h1, h8⟩
      · have h' : c < x := by linarith
        have h1 : c + (δ : ℝ) ∈ D := Or.inr ⟨c, hc, by ring⟩
        have h2 : |x - (c + (δ : ℝ))| ≤ (δ : ℝ) := by
          have h3 : x - c ≤ 2 * (δ : ℝ) := by
            have h4 : |x - c| ≤ 2 * (δ : ℝ) := h_ineq
            have h5 : x - c = |x - c| := by
              rw [abs_of_nonneg (show 0 ≤ x - c by linarith)] <;> linarith
            linarith
          have h6 : x - (c + (δ : ℝ)) = (x - c) - (δ : ℝ) := by ring
          rw [h6]
          rw [abs_le] <;> constructor <;> linarith
        have h7 : dist x (c + (δ : ℝ)) ≤ (δ : ℝ) := by simpa [dist_eq_norm] using h2
        have h8 : edist x (c + (δ : ℝ)) ≤ ↑δ := dist_le_to_edist_le h7
        exact ⟨c + (δ : ℝ), h1, h8⟩
    have h1 : Metric.externalCoveringNumber δ S ≤ D.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hD_cover
    have h2 : D.encard ≤ ((fun x : ℝ => x - (δ : ℝ)) '' C).encard + ((fun x : ℝ => x + (δ : ℝ)) '' C).encard :=
      Set.encard_union_le _ _
    have h3 : ((fun x : ℝ => x - (δ : ℝ)) '' C).encard ≤ C.encard := Set.encard_image_le _ _
    have h4 : ((fun x : ℝ => x + (δ : ℝ)) '' C).encard ≤ C.encard := Set.encard_image_le _ _
    have h5 : D.encard ≤ C.encard + C.encard := by
      calc D.encard
        ≤ ((fun x : ℝ => x - (δ : ℝ)) '' C).encard + ((fun x : ℝ => x + (δ : ℝ)) '' C).encard := h2
      _ ≤ C.encard + C.encard := by gcongr
    have h6 : C.encard + C.encard = 2 * C.encard := by ring
    rw [h6] at h5
    rw [hC_eq] at h5
    exact h1.trans h5

/-- Local Lipschitz image covering: covering_{2Kε}(f '' S) ≤ covering_ε(S). -/
lemma externalCoveringNumber_image_lipschitz_on
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : NNReal} {S : Set X} {ε : NNReal}
    (hS_nonempty : S.Nonempty)
    (hf : ∀ x y, x ∈ S → y ∈ S → dist (f x) (f y) ≤ (K : ℝ) * dist x y) :
    Metric.externalCoveringNumber (2 * K * ε) (f '' S) ≤
      Metric.externalCoveringNumber ε S := by
  by_cases h_top : Metric.externalCoveringNumber ε S = ⊤
  · rw [h_top] <;> simp
  · have hfin : Metric.externalCoveringNumber ε S < ⊤ := lt_top_iff_ne_top.mpr h_top
    rcases exists_external_cover_eq hfin with ⟨C, hC, hC_eq⟩
    have hC_finite : C.Finite := by
      have h : C.encard < ⊤ := by rw [hC_eq] <;> exact hfin
      exact Set.encard_lt_top_iff.mp h
    classical
    let C' : Finset X := hC_finite.toFinset
    have hC'_eq : (C' : Set X) = C := hC_finite.coe_toFinset
    let relevant (c : X) : Prop := (Metric.closedBall c ε : Set X) ∩ S ≠ ∅
    have hP : ∀ (c : X), relevant c → ∃ (x : X), x ∈ (Metric.closedBall c ε : Set X) ∩ S := by
      intro c hc
      dsimp only [relevant] at hc
      exact Set.nonempty_iff_ne_empty.mpr hc
    choose x hx using hP
    let g : X → X := fun c =>
      if hc : relevant c then x c hc else Classical.choose hS_nonempty
    let D : Finset X := Finset.image g C'
    have hD_eq : (D : Set X) = g '' (C' : Set X) := by
      simp [D, Finset.coe_image] <;> rfl
    have hD_subset : ∀ d ∈ (D : Set X), d ∈ S := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨c, hc, rfl⟩
      by_cases hrel : relevant c
      · simpa [g, hrel] using (hx c hrel).2
      · simpa [g, hrel] using Classical.choose_spec hS_nonempty
    have hD_cover : Metric.IsCover (2 * ε) S (D : Set X) := by
      intro y hy
      have hC' : ∃ (c : X), c ∈ C ∧ (y, c) ∈ {(p : X × X) | edist p.1 p.2 ≤ ↑ε} := hC hy
      rcases hC' with ⟨c, hc, hedistance⟩
      have h_edist : edist y c ≤ ↑ε := by simpa using hedistance
      have hdist : dist y c ≤ (ε : ℝ) := edist_le_to_dist_le h_edist
      have h1 : y ∈ (Metric.closedBall c ε : Set X) ∩ S :=
        ⟨by simpa [Metric.mem_closedBall] using hdist, hy⟩
      have h_nonempty : ((Metric.closedBall c ε : Set X) ∩ S).Nonempty := ⟨y, h1⟩
      have hrel : relevant c := Set.nonempty_iff_ne_empty.mp h_nonempty
      have h2 : dist y (g c) ≤ 2 * (ε : ℝ) := by
        have h3 : dist (x c hrel) c ≤ (ε : ℝ) := by
          have h4 : (x c hrel) ∈ (Metric.closedBall c ε : Set X) := (hx c hrel).1
          simpa [Metric.mem_closedBall] using h4
        have h5 : dist y (g c) ≤ dist y c + dist c (g c) := dist_triangle y c (g c)
        have h6 : dist c (g c) = dist (x c hrel) c := by
          simp [g, hrel, dist_comm]
        rw [h6] at h5
        linarith
      have hc' : c ∈ C' := by
        have h : c ∈ (C' : Set X) := by rw [hC'_eq]; exact hc
        exact_mod_cast h
      have h5 : g c ∈ (D : Set X) := Finset.mem_image_of_mem g hc'
      have h6 : edist y (g c) ≤ ↑(2 * ε) := dist_le_to_edist_le h2
      exact ⟨g c, h5, h6⟩
    let E : Set Y := f '' (D : Set X)
    have hE_cover : Metric.IsCover (2 * K * ε) (f '' S) E := by
      intro z hz
      rcases hz with ⟨y, hy, rfl⟩
      rcases hD_cover hy with ⟨d, hd, hedistance⟩
      have h_edist : edist y d ≤ ↑(2 * ε) := by simpa using hedistance
      have hdist : dist y d ≤ 2 * (ε : ℝ) := edist_le_to_dist_le h_edist
      have h6 : dist (f y) (f d) ≤ (K : ℝ) * (2 * (ε : ℝ)) := by
        calc dist (f y) (f d)
          ≤ (K : ℝ) * dist y d := hf y d hy (hD_subset d hd)
        _ ≤ (K : ℝ) * (2 * (ε : ℝ)) := by gcongr
      have h7 : f d ∈ E := ⟨d, hd, rfl⟩
      have h9 : (K : ℝ) * (2 * (ε : ℝ)) = ↑(2 * K * ε) := by
        simp [NNReal.coe_mul] <;> ring
      have h10 : dist (f y) (f d) ≤ ↑(2 * K * ε) := by
        rw [h9] at h6
        exact h6
      have h8 : edist (f y) (f d) ≤ ↑(2 * K * ε) := by
        have h11 : edist (f y) (f d) = ENNReal.ofReal (dist (f y) (f d)) := edist_dist (f y) (f d)
        rw [h11]
        have h12 : (↑(2 * K * ε) : ENNReal) = ENNReal.ofReal (↑(2 * K * ε) : ℝ) := by simp
        rw [h12]
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mpr h10
      exact ⟨f d, h7, h8⟩
    have h1 : Metric.externalCoveringNumber (2 * K * ε) (f '' S) ≤ E.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hE_cover
    have h2 : E.encard ≤ (D : Set X).encard := Set.encard_image_le f (D : Set X)
    have h3 : (D : Set X).encard ≤ (C' : Set X).encard := by
      rw [hD_eq]; exact Set.encard_image_le g (C' : Set X)
    have h4 : (C' : Set X).encard = C.encard := by rw [hC'_eq]
    rw [h4] at h3
    have h5 : E.encard ≤ C.encard := h2.trans h3
    rw [hC_eq] at h5
    exact h1.trans h5

/-! ### Main theorem -/

/-- ENNReal algebra lemma for tubesAndSlopes_converse:
    4 * C * (70*r)^s * (500 * A) ≤ 200000*C * r^s * A -/
lemma enreal_algebra_lemma (C r : ℝ) (s : ℝ) (A : ENNReal)
    (hC_pos : 0 < C) (hr_pos : 0 < r) (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1) :
    (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal (70 * r)) ^ s * ((500 : ENNReal) * A)) ≤
    ENNReal.ofReal (200000 * C) * (ENNReal.ofReal r) ^ s * A := by
  have h_rpow70 : (ENNReal.ofReal (70 * r)) ^ s =
      (ENNReal.ofReal 70) ^ s * (ENNReal.ofReal r) ^ s := by
    have h2 : ENNReal.ofReal (70 * r) = ENNReal.ofReal 70 * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h2]
    exact ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal 70) (ENNReal.ofReal r) hs_nonneg
  have h3 : (ENNReal.ofReal 70) ^ s ≤ ENNReal.ofReal 70 := by
    have h4 : (ENNReal.ofReal 70) ^ s ≤ (ENNReal.ofReal 70) ^ (1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hs_le_one
    have h5 : (ENNReal.ofReal 70) ^ (1 : ℝ) = ENNReal.ofReal 70 := by simp
    rw [h5] at h4; exact h4
  rw [h_rpow70]
  set B := ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * A with hB
  have h4 : (4 : ENNReal) * (ENNReal.ofReal C * ((ENNReal.ofReal 70) ^ s * (ENNReal.ofReal r) ^ s) *
        ((500 : ENNReal) * A)) =
      (4 * 500 : ENNReal) * (ENNReal.ofReal 70) ^ s * B := by
    simp [B, mul_assoc, mul_comm, mul_left_comm]
  rw [h4]
  have h5 : (4 * 500 : ENNReal) * (ENNReal.ofReal 70) ^ s ≤ (4 * 500 * 70 : ENNReal) := by
    calc (4 * 500 : ENNReal) * (ENNReal.ofReal 70) ^ s
      ≤ (4 * 500 : ENNReal) * ENNReal.ofReal 70 := by gcongr
    _ = (4 * 500 * 70 : ENNReal) := by norm_num
  have h6 : (4 * 500 * 70 : ENNReal) * ENNReal.ofReal C ≤ ENNReal.ofReal (200000 * C) := by
    have h7 : (4 * 500 * 70 : ENNReal) * ENNReal.ofReal C = ENNReal.ofReal ((4 * 500 * 70 : ℝ) * C) := by
      simp [ENNReal.ofReal_mul] <;> ring
    rw [h7]
    apply ENNReal.ofReal_le_ofReal
    have h8 : (4 * 500 * 70 : ℝ) * C ≤ 200000 * C := by
      gcongr <;> norm_num
    exact h8
  have h_final1 : (4 * 500 : ENNReal) * (ENNReal.ofReal 70) ^ s * B ≤
      (4 * 500 * 70 : ENNReal) * B := by exact mul_le_mul_left h5 B
  have h_final2 : (4 * 500 * 70 : ENNReal) * B ≤
      ENNReal.ofReal (200000 * C) * (ENNReal.ofReal r) ^ s * A := by
    have hB' : B = ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * A := by rfl
    rw [hB']
    have h9 : (4 * 500 * 70 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * A) =
        ((4 * 500 * 70 : ENNReal) * ENNReal.ofReal C) * (ENNReal.ofReal r) ^ s * A := by
      simp [mul_assoc]
    rw [h9]
    gcongr <;> exact h6
  exact le_trans h_final1 h_final2

/-- Converse direction of tubesAndSlopes:
    If a family of affine lines all pass within δ of a common point p ∈ unit ball,
    and all have bounded slope, then the slope projection is an S-set. -/
lemma tubesAndSlopes_converse
    {δ s C : ℝ} {T : Set AffineLine} {p : Plane}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hC_pos : 0 < C)
    (hT : IsDeltaSSet δ s C T)
    (hp : p ∈ Metric.closedBall 0 1)
    (h_near : ∀ ℓ ∈ T, p ∈ Metric.cthickening δ ℓ.1)
    (h_slope : ∀ ℓ ∈ T, (getDirV ℓ) 1 ≠ 0 ∧ |(affineLineParams ℓ).1| ≤ 1) :
    IsDeltaSSet δ s (200000 * C) ((fun ℓ => (affineLineParams ℓ).1) '' T) := by
  let f : AffineLine → ℝ := fun ℓ => (affineLineParams ℓ).1
  let A : Set ℝ := f '' T
  have hT_nonempty : T.Nonempty := hT.1
  have hA_nonempty : A.Nonempty := hT_nonempty.image f
  have h_f_lip : ∀ ℓ₁ ℓ₂, ℓ₁ ∈ T → ℓ₂ ∈ T → dist (f ℓ₁) (f ℓ₂) ≤ 2 * dist ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂ h₁ h₂
    have h1_v1 := (h_slope ℓ₁ h₁).1
    have h2_v1 := (h_slope ℓ₂ h₂).1
    have h1_s := (h_slope ℓ₁ h₁).2
    have h2_s := (h_slope ℓ₂ h₂).2
    exact slope_lipschitz ℓ₁ ℓ₂ h1_v1 h2_v1 h1_s h2_s
  have h_v1' : ∀ ℓ ∈ T, (getDirV ℓ) 1 ≠ 0 := fun ℓ hℓ => (h_slope ℓ hℓ).1
  have h_slope' : ∀ ℓ ∈ T, |(affineLineParams ℓ).1| ≤ 1 := fun ℓ hℓ => (h_slope ℓ hℓ).2
  -- Global transfer: covering_δ(T) ≤ 500 * covering_δ(A)
  have h_global : Metric.externalCoveringNumber δ.toNNReal T ≤
      500 * Metric.externalCoveringNumber δ.toNNReal A := by
    by_cases h_top : Metric.externalCoveringNumber δ.toNNReal A = ⊤
    · rw [h_top] <;> simp
    · have hfin : Metric.externalCoveringNumber δ.toNNReal A < ⊤ := lt_top_iff_ne_top.mpr h_top
      rcases exists_external_cover_eq hfin with ⟨C_set, hC_cover, hC_eq⟩
      have hC_finite : C_set.Finite := by
        have h : C_set.encard < ⊤ := by rw [hC_eq] <;> exact hfin
        exact Set.encard_lt_top_iff.mp h
      classical
      let C_fin : Finset ℝ := hC_finite.toFinset
      have hC_fin_eq : (C_fin : Set ℝ) = C_set := hC_finite.coe_toFinset
      let D : Finset AffineLine := C_fin.biUnion fun a_center =>
        Classical.choose (strip_covering p δ hδ_pos hp hδ_le_one T h_near h_slope' h_v1' a_center)
      have hD_cover : Metric.IsCover δ.toNNReal T D := by
        intro ℓ hℓ
        have h_a_in_A : f ℓ ∈ A := ⟨ℓ, hℓ, rfl⟩
        rcases hC_cover h_a_in_A with ⟨c, hc, hedistance⟩
        have hdist : dist (f ℓ) c ≤ (δ.toNNReal : ℝ) := edist_le_to_dist_le hedistance
        have h_strip : |f ℓ - c| ≤ δ := by
          have h_eq : dist (f ℓ) c = |f ℓ - c| := by
            simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl
          rw [h_eq] at hdist
          have h_coe : (δ.toNNReal : ℝ) = δ := by
            have h_nonneg : 0 ≤ δ := by linarith
            have h : (δ.toNNReal : ℝ) = max δ 0 := by exact Real.coe_toNNReal' δ
            rw [h, max_eq_left h_nonneg]
          rw [h_coe] at hdist
          exact hdist
        let D_c := Classical.choose (strip_covering p δ hδ_pos hp hδ_le_one T h_near h_slope' h_v1' c)
        have hD_c_cover : Metric.IsCover δ.toNNReal (T ∩ {ℓ | |f ℓ - c| ≤ δ}) D_c :=
          (Classical.choose_spec (strip_covering p δ hδ_pos hp hδ_le_one T h_near h_slope' h_v1' c)).1
        have hℓ_in_strip : ℓ ∈ T ∩ {ℓ | |f ℓ - c| ≤ δ} := ⟨hℓ, h_strip⟩
        rcases hD_c_cover hℓ_in_strip with ⟨ℓ_g, hℓg_in_Dc, hedist2⟩
        have hℓg_in_D : ℓ_g ∈ D := by
          apply Finset.mem_biUnion.mpr
          refine ⟨c, ?_, hℓg_in_Dc⟩
          have hc' : c ∈ (C_fin : Set ℝ) := by
            rw [hC_fin_eq]
            exact hc
          exact_mod_cast hc'
        exact ⟨ℓ_g, hℓg_in_D, hedist2⟩
      have hD_card : D.card ≤ 500 * C_fin.card := by
        calc D.card
          ≤ ∑ a ∈ C_fin, (Classical.choose (strip_covering p δ hδ_pos hp hδ_le_one T h_near h_slope' h_v1' a)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ C_fin, 500 := by
          apply Finset.sum_le_sum
          intro a _
          exact (Classical.choose_spec (strip_covering p δ hδ_pos hp hδ_le_one T h_near h_slope' h_v1' a)).2
        _ = 500 * C_fin.card := by simp [Finset.sum_const] <;> ring
      have h1 : Metric.externalCoveringNumber δ.toNNReal T ≤ (D : Set AffineLine).encard :=
        hD_cover.externalCoveringNumber_le_encard
      have h2 : (D : Set AffineLine).encard ≤ 500 * C_set.encard := by
        have h3 : (D : Set AffineLine).encard = ↑D.card := by exact Set.encard_coe_eq_coe_finsetCard D
        rw [h3]
        have h4 : C_set.encard = ↑C_fin.card := by
          rw [← hC_fin_eq] <;> exact Set.encard_coe_eq_coe_finsetCard C_fin
        rw [h4]
        exact_mod_cast hD_card
      rw [hC_eq] at h2
      exact h1.trans h2
  -- Image covering bound: covering_δ(f '' S) ≤ 4 * covering_δ(S) for S ⊆ T
  have h_image_bound : ∀ (S : Set AffineLine), S.Nonempty → S ⊆ T →
      Metric.externalCoveringNumber δ.toNNReal (f '' S) ≤
        4 * Metric.externalCoveringNumber δ.toNNReal S := by
    intro S hS_nonempty hS_sub
    let K : NNReal := 2
    have h_lip_on : ∀ (x y : AffineLine), x ∈ S → y ∈ S →
        dist (f x) (f y) ≤ (K : ℝ) * dist x y := by
      intro x y hx hy
      have h := h_f_lip x y (hS_sub hx) (hS_sub hy)
      simpa [K] using h
    have h1 : Metric.externalCoveringNumber (2 * K * δ.toNNReal) (f '' S) ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
      exact @externalCoveringNumber_image_lipschitz_on AffineLine ℝ _ _ f K S δ.toNNReal hS_nonempty h_lip_on
    have hK_eq : (2 * K * δ.toNNReal : NNReal) = 4 * δ.toNNReal := by
      have hK2 : 2 * K = (4 : NNReal) := by
        apply NNReal.coe_injective
        have h : ((2 * K : NNReal) : ℝ) = 4 := by
          simp [K] <;> norm_num
        exact_mod_cast h
      rw [hK2] <;> ring
    let imgS : Set ℝ := f '' S
    let δ2 : NNReal := 2 * δ.toNNReal
    let δ4 : NNReal := 4 * δ.toNNReal
    have h2 : Metric.externalCoveringNumber δ.toNNReal imgS ≤
        2 * Metric.externalCoveringNumber δ2 imgS :=
      @real_covering_doubling imgS δ.toNNReal (by positivity)
    have h3 : Metric.externalCoveringNumber δ2 imgS ≤
        2 * Metric.externalCoveringNumber δ4 imgS := by
      have h := @real_covering_doubling imgS δ2 (by positivity)
      have h_eq : (2 * δ2 : NNReal) = δ4 := by
        simp [δ2, δ4] <;> ring
      rw [h_eq] at h
      exact h
    have h4 : Metric.externalCoveringNumber δ4 imgS ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
      have h6 : δ4 = 4 * δ.toNNReal := by rfl
      have h7 : (4 * δ.toNNReal : NNReal) = 2 * K * δ.toNNReal := hK_eq.symm
      rw [h6, h7]
      exact h1
    calc Metric.externalCoveringNumber δ.toNNReal imgS
      ≤ 2 * Metric.externalCoveringNumber δ2 imgS := h2
    _ ≤ 2 * (2 * Metric.externalCoveringNumber δ4 imgS) := by gcongr
    _ = 4 * Metric.externalCoveringNumber δ4 imgS := by ring
    _ ≤ 4 * Metric.externalCoveringNumber δ.toNNReal S := by gcongr
  -- Main S-set property
  refine' ⟨hA_nonempty, hδ_pos, by positivity, hs_nonneg, _⟩
  intro x r hr
  by_cases h_nonempty : (A ∩ Metric.closedBall x r).Nonempty
  · rcases h_nonempty with ⟨a₀, ha₀⟩
    have ha₀_A : a₀ ∈ A := ha₀.1
    have ha₀_ball : a₀ ∈ Metric.closedBall x r := ha₀.2
    have h_dist_eq : ∀ (y z : ℝ), dist y z = |y - z| := by
      intro y z
      simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl
    rcases ha₀_A with ⟨ℓ₀, hℓ₀_T, rfl⟩
    have h' : |f ℓ₀ - x| ≤ r := by
      have h_eq : dist (f ℓ₀) x = |f ℓ₀ - x| := h_dist_eq (f ℓ₀) x
      have h : dist (f ℓ₀) x ≤ r := ha₀_ball
      rw [h_eq] at h
      exact h
    let S : Set AffineLine := T ∩ {ℓ | |f ℓ - x| ≤ r}
    have hℓ₀_in_S : ℓ₀ ∈ S := ⟨hℓ₀_T, h'⟩
    have hS_nonempty : S.Nonempty := ⟨ℓ₀, hℓ₀_in_S⟩
    have hS_sub : S ⊆ T := by intro ℓ hℓ; exact hℓ.1
    have hS1 : A ∩ Metric.closedBall x r = f '' S := by
      ext y
      simp only [A, S, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨ℓ, hℓ, rfl⟩, hball⟩
        refine ⟨ℓ, ⟨hℓ, ?_⟩, rfl⟩
        have h : dist (f ℓ) x ≤ r := hball
        have h' : |f ℓ - x| ≤ r := by
          rw [←h_dist_eq (f ℓ) x]
          exact h
        exact h'
      · rintro ⟨ℓ, ⟨hℓ, hstrip⟩, rfl⟩
        have h : dist (f ℓ) x ≤ r := by
          rw [h_dist_eq (f ℓ) x]
          exact hstrip
        exact ⟨⟨ℓ, hℓ, rfl⟩, h⟩
    have hS2 : S ⊆ Metric.closedBall ℓ₀ (70 * r) := by
      intro ℓ hℓ
      have hℓ_T : ℓ ∈ T := hℓ.1
      have hstrip : |f ℓ - x| ≤ r := hℓ.2
      have h1_v1 := (h_slope ℓ hℓ_T).1
      have h2_v1 := (h_slope ℓ₀ hℓ₀_T).1
      have h1_s := (h_slope ℓ hℓ_T).2
      have h2_s := (h_slope ℓ₀ hℓ₀_T).2
      have h_near1 := h_near ℓ hℓ_T
      have h_near2 := h_near ℓ₀ hℓ₀_T
      have h_dist : dist ℓ ℓ₀ ≤ 30 * |f ℓ - f ℓ₀| + 10 * δ :=
        dist_bound_near_point ℓ ℓ₀ p δ hδ_pos hp h_near1 h_near2 h1_v1 h2_v1 h1_s h2_s
      have h_slope_diff : |f ℓ - f ℓ₀| ≤ 2 * r := by
        have h1 : |f ℓ - f ℓ₀| ≤ |f ℓ - x| + |x - f ℓ₀| := by exact abs_sub_le (f ℓ) x (f ℓ₀)
        have h2 : |x - f ℓ₀| ≤ r := by
          have h3 : |f ℓ₀ - x| ≤ r := hℓ₀_in_S.2
          rw [show x - f ℓ₀ = -(f ℓ₀ - x) by ring]
          rw [abs_neg]
          exact h3
        linarith
      have h3 : dist ℓ ℓ₀ ≤ 70 * r := by
        calc dist ℓ ℓ₀ ≤ 30 * |f ℓ - f ℓ₀| + 10 * δ := h_dist
          _ ≤ 30 * (2 * r) + 10 * δ := by gcongr
          _ = 60 * r + 10 * δ := by ring
          _ ≤ 70 * r := by linarith [hr]
      simpa [Metric.mem_closedBall] using h3
    have hS2' : S ⊆ T ∩ Metric.closedBall ℓ₀ (70 * r) := by
      intro ℓ hℓ
      exact ⟨hℓ.1, hS2 hℓ⟩
    have hT_sset := hT.2.2.2.2
    have h4 : Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall ℓ₀ (70 * r)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (70 * r)) ^ s *
          Metric.externalCoveringNumber δ.toNNReal T :=
      hT_sset ℓ₀ (70 * r) (by linarith [hr])
    have h5 : Metric.externalCoveringNumber δ.toNNReal S ≤
        Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall ℓ₀ (70 * r)) :=
      Metric.externalCoveringNumber_mono_set hS2'
    have h6 : Metric.externalCoveringNumber δ.toNNReal (f '' S) ≤
        4 * Metric.externalCoveringNumber δ.toNNReal S :=
      h_image_bound S hS_nonempty hS_sub
    have h7 : (ENNReal.ofReal (70 * r)) ^ s ≤ ENNReal.ofReal 70 * (ENNReal.ofReal r) ^ s := by
      have hr_nonneg : 0 ≤ r := by linarith [hr]
      have h_ineq : (70 * r) ^ s ≤ 70 * r ^ s := by
        have h1 : ((70 : ℝ) * r) ^ s = (70 : ℝ) ^ s * r ^ s := by
          rw [Real.mul_rpow] <;> linarith
        rw [h1]
        have h2 : (70 : ℝ) ^ s ≤ (70 : ℝ) := by
          have h21 : (70 : ℝ) ^ s ≤ (70 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hs_le_one
          have h22 : (70 : ℝ) ^ (1 : ℝ) = (70 : ℝ) := by simp
          rw [h22] at h21
          exact h21
        have h3 : 0 ≤ r ^ s := Real.rpow_nonneg (by linarith) s
        exact mul_le_mul_of_nonneg_right h2 h3
      have h4' : ENNReal.ofReal ((70 * r) ^ s) ≤ ENNReal.ofReal (70 * r ^ s) :=
        ENNReal.ofReal_le_ofReal h_ineq
      have h5' : (ENNReal.ofReal (70 * r)) ^ s = ENNReal.ofReal ((70 * r) ^ s) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg
      have h6' : ENNReal.ofReal (70 * r ^ s) = ENNReal.ofReal 70 * (ENNReal.ofReal r) ^ s := by
        have h71 : ENNReal.ofReal (70 * r ^ s) = ENNReal.ofReal 70 * ENNReal.ofReal (r ^ s) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [h71]
        have h8 : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
          ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs_nonneg
        rw [h8]
      rw [h5']
      exact h4'.trans (le_of_eq h6')
    let eT : Set AffineLine → ENNReal := fun S => (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)
    let eR : Set ℝ → ENNReal := fun S => (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)
    have h4' : eT (T ∩ Metric.closedBall ℓ₀ (70 * r)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (70 * r)) ^ s * eT T := by
      dsimp only [eT]
      exact_mod_cast h4
    have h5' : eT S ≤ eT (T ∩ Metric.closedBall ℓ₀ (70 * r)) := by
      have h5_cast : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall ℓ₀ (70 * r)) : ENNReal) :=
        by exact_mod_cast h5
      simpa [eT] using h5_cast
    have h6' : eR (f '' S) ≤ (4 : ENNReal) * eT S := by
      dsimp only [eR, eT]
      have h : (Metric.externalCoveringNumber δ.toNNReal (f '' S) : ENNReal) ≤
          ((4 * Metric.externalCoveringNumber δ.toNNReal S : ℕ∞) : ENNReal) := by
        exact_mod_cast h6
      have h2 : ((4 * Metric.externalCoveringNumber δ.toNNReal S : ℕ∞) : ENNReal) =
          (4 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
        simp
      rw [h2] at h
      exact h
    have h_global' : eT T ≤ (500 : ENNReal) * eR A := by
      dsimp only [eT, eR]
      have h : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
          ((500 * Metric.externalCoveringNumber δ.toNNReal A : ℕ∞) : ENNReal) := by
        exact_mod_cast h_global
      have h2 : ((500 * Metric.externalCoveringNumber δ.toNNReal A : ℕ∞) : ENNReal) =
          (500 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
        simp
      rw [h2] at h
      exact h
    have h_mul1 : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal 70 * (ENNReal.ofReal r) ^ s) * eT T) =
        ENNReal.ofReal (280 * C) * (ENNReal.ofReal r) ^ s * eT T := by
      have h9 : (4 : ENNReal) = ENNReal.ofReal 4 := by norm_cast
      rw [h9]
      have h_posC : 0 ≤ C := by linarith
      have h10 : ENNReal.ofReal 4 * (ENNReal.ofReal C * (ENNReal.ofReal 70 * (ENNReal.ofReal r) ^ s) * eT T) =
          (ENNReal.ofReal 4 * ENNReal.ofReal C * ENNReal.ofReal 70) * ((ENNReal.ofReal r) ^ s * eT T) := by
        simp only [mul_assoc]
        <;> ac_rfl
      rw [h10]
      have h11 : ENNReal.ofReal 4 * ENNReal.ofReal C * ENNReal.ofReal 70 = ENNReal.ofReal (280 * C) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num),
            ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 * C by positivity)]
        <;> norm_cast <;> ring_nf
      rw [h11]
      <;> ac_rfl
    have h_mul2 : ENNReal.ofReal (280 * C) * (ENNReal.ofReal r) ^ s * ((500 : ENNReal) * eR A) =
        ENNReal.ofReal (140000 * C) * (ENNReal.ofReal r) ^ s * eR A := by
      have h13 : (500 : ENNReal) = ENNReal.ofReal 500 := by norm_cast
      rw [h13]
      have h14 : ENNReal.ofReal (280 * C) * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal 500 * eR A) =
          (ENNReal.ofReal (280 * C) * ENNReal.ofReal 500) * ((ENNReal.ofReal r) ^ s * eR A) := by
        simp only [mul_assoc] <;> ac_rfl
      rw [h14]
      have h15 : ENNReal.ofReal (280 * C) * ENNReal.ofReal 500 = ENNReal.ofReal (140000 * C) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 280 * C by positivity)]
        <;> norm_cast <;> ring_nf
      rw [h15] <;> ac_rfl
    calc eR (A ∩ Metric.closedBall x r)
      = eR (f '' S) := by rw [hS1]
    _ ≤ (4 : ENNReal) * eT S := h6'
    _ ≤ (4 : ENNReal) * eT (T ∩ Metric.closedBall ℓ₀ (70 * r)) := by
      exact mul_le_mul_of_nonneg_left h5' (by positivity)
    _ ≤ (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal (70 * r)) ^ s * eT T) := by
      exact mul_le_mul_of_nonneg_left h4' (by positivity)
    _ ≤ (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal 70 * (ENNReal.ofReal r) ^ s) * eT T) := by
      gcongr
      <;> exact h7
    _ = ENNReal.ofReal (280 * C) * (ENNReal.ofReal r) ^ s * eT T := h_mul1
    _ ≤ ENNReal.ofReal (280 * C) * (ENNReal.ofReal r) ^ s * ((500 : ENNReal) * eR A) := by
      gcongr
      <;> exact h_global'
    _ = ENNReal.ofReal (140000 * C) * (ENNReal.ofReal r) ^ s * eR A := h_mul2
    _ ≤ ENNReal.ofReal (200000 * C) * (ENNReal.ofReal r) ^ s * eR A := by
      have h140 : 140000 * C ≤ 200000 * C := by
        have hC_nonneg : 0 ≤ C := by linarith [hC_pos]
        nlinarith
      have h141 : ENNReal.ofReal (140000 * C) ≤ ENNReal.ofReal (200000 * C) := by
        gcongr
        <;> nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h141 (by positivity)) (by positivity)
  · have h_eq : (A ∩ Metric.closedBall x r) = ∅ := by
      by_contra h
      have h' : (A ∩ Metric.closedBall x r).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h
      exact h_nonempty h'
    rw [Metric.externalCoveringNumber_eq_zero.mpr h_eq]
    <;> simp

/-- R2 variant: slopes form a δ-S-set when lines are near a point p with ‖p‖ ≤ 2.
    Constant: 400000*C. -/
lemma tubesAndSlopes_converse_R2
    {δ s C : ℝ} {T : Set AffineLine} {p : Plane}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hs_nonneg : 0 ≤ s) (hs_le_one : s ≤ 1)
    (hC_pos : 0 < C)
    (hT : IsDeltaSSet δ s C T)
    (hR : ‖p‖ ≤ 2)
    (h_near : ∀ ℓ ∈ T, p ∈ Metric.cthickening δ ℓ.1)
    (h_slope : ∀ ℓ ∈ T, (getDirV ℓ) 1 ≠ 0 ∧ |(affineLineParams ℓ).1| ≤ 1) :
    IsDeltaSSet δ s (400000 * C) ((fun ℓ => (affineLineParams ℓ).1) '' T) := by
  let f : AffineLine → ℝ := fun ℓ => (affineLineParams ℓ).1
  let A : Set ℝ := f '' T
  have hT_nonempty : T.Nonempty := hT.1
  have hA_nonempty : A.Nonempty := hT_nonempty.image f
  have h_f_lip : ∀ ℓ₁ ℓ₂, ℓ₁ ∈ T → ℓ₂ ∈ T → dist (f ℓ₁) (f ℓ₂) ≤ 2 * dist ℓ₁ ℓ₂ := by
    intro ℓ₁ ℓ₂ h₁ h₂
    have h1_v1 := (h_slope ℓ₁ h₁).1
    have h2_v1 := (h_slope ℓ₂ h₂).1
    have h1_s := (h_slope ℓ₁ h₁).2
    have h2_s := (h_slope ℓ₂ h₂).2
    exact slope_lipschitz ℓ₁ ℓ₂ h1_v1 h2_v1 h1_s h2_s
  have h_v1' : ∀ ℓ ∈ T, (getDirV ℓ) 1 ≠ 0 := fun ℓ hℓ => (h_slope ℓ hℓ).1
  have h_slope' : ∀ ℓ ∈ T, |(affineLineParams ℓ).1| ≤ 1 := fun ℓ hℓ => (h_slope ℓ hℓ).2
  -- Global transfer: covering_δ(T) ≤ 600 * covering_δ(A)
  have h_global : Metric.externalCoveringNumber δ.toNNReal T ≤
      600 * Metric.externalCoveringNumber δ.toNNReal A := by
    by_cases h_top : Metric.externalCoveringNumber δ.toNNReal A = ⊤
    · rw [h_top] <;> simp
    · have hfin : Metric.externalCoveringNumber δ.toNNReal A < ⊤ := lt_top_iff_ne_top.mpr h_top
      rcases exists_external_cover_eq hfin with ⟨C_set, hC_cover, hC_eq⟩
      have hC_finite : C_set.Finite := by
        have h : C_set.encard < ⊤ := by rw [hC_eq] <;> exact hfin
        exact Set.encard_lt_top_iff.mp h
      classical
      let C_fin : Finset ℝ := hC_finite.toFinset
      have hC_fin_eq : (C_fin : Set ℝ) = C_set := hC_finite.coe_toFinset
      let D : Finset AffineLine := C_fin.biUnion fun a_center =>
        Classical.choose (strip_covering_R2 p δ hδ_pos hR hδ_le_one T h_near h_slope' h_v1' a_center)
      have hD_cover : Metric.IsCover δ.toNNReal T D := by
        intro ℓ hℓ
        have h_a_in_A : f ℓ ∈ A := ⟨ℓ, hℓ, rfl⟩
        rcases hC_cover h_a_in_A with ⟨c, hc, hedistance⟩
        have hdist : dist (f ℓ) c ≤ (δ.toNNReal : ℝ) := edist_le_to_dist_le hedistance
        have h_strip : |f ℓ - c| ≤ δ := by
          have h_eq : dist (f ℓ) c = |f ℓ - c| := by
            simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl
          rw [h_eq] at hdist
          have h_coe : (δ.toNNReal : ℝ) = δ := by
            have h_nonneg : 0 ≤ δ := by linarith
            have h : (δ.toNNReal : ℝ) = max δ 0 := by exact Real.coe_toNNReal' δ
            rw [h, max_eq_left h_nonneg]
          rw [h_coe] at hdist
          exact hdist
        let D_c := Classical.choose (strip_covering_R2 p δ hδ_pos hR hδ_le_one T h_near h_slope' h_v1' c)
        have hD_c_cover : Metric.IsCover δ.toNNReal (T ∩ {ℓ | |f ℓ - c| ≤ δ}) D_c :=
          (Classical.choose_spec (strip_covering_R2 p δ hδ_pos hR hδ_le_one T h_near h_slope' h_v1' c)).1
        have hℓ_in_strip : ℓ ∈ T ∩ {ℓ | |f ℓ - c| ≤ δ} := ⟨hℓ, h_strip⟩
        rcases hD_c_cover hℓ_in_strip with ⟨ℓ_g, hℓg_in_Dc, hedist2⟩
        have hℓg_in_D : ℓ_g ∈ D := by
          apply Finset.mem_biUnion.mpr
          refine ⟨c, ?_, hℓg_in_Dc⟩
          have hc' : c ∈ (C_fin : Set ℝ) := by
            rw [hC_fin_eq]
            exact hc
          exact_mod_cast hc'
        exact ⟨ℓ_g, hℓg_in_D, hedist2⟩
      have hD_card : D.card ≤ 600 * C_fin.card := by
        calc D.card
          ≤ ∑ a ∈ C_fin, (Classical.choose (strip_covering_R2 p δ hδ_pos hR hδ_le_one T h_near h_slope' h_v1' a)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ C_fin, 600 := by
          apply Finset.sum_le_sum
          intro a _
          exact (Classical.choose_spec (strip_covering_R2 p δ hδ_pos hR hδ_le_one T h_near h_slope' h_v1' a)).2
        _ = 600 * C_fin.card := by simp [Finset.sum_const] <;> ring
      have h1 : Metric.externalCoveringNumber δ.toNNReal T ≤ (D : Set AffineLine).encard :=
        hD_cover.externalCoveringNumber_le_encard
      have h2 : (D : Set AffineLine).encard ≤ 600 * C_set.encard := by
        have h3 : (D : Set AffineLine).encard = ↑D.card := by exact Set.encard_coe_eq_coe_finsetCard D
        rw [h3]
        have h4 : C_set.encard = ↑C_fin.card := by
          rw [← hC_fin_eq] <;> exact Set.encard_coe_eq_coe_finsetCard C_fin
        rw [h4]
        exact_mod_cast hD_card
      rw [hC_eq] at h2
      exact h1.trans h2
  -- Image covering bound: covering_δ(f '' S) ≤ 4 * covering_δ(S) for S ⊆ T
  have h_image_bound : ∀ (S : Set AffineLine), S.Nonempty → S ⊆ T →
      Metric.externalCoveringNumber δ.toNNReal (f '' S) ≤
        4 * Metric.externalCoveringNumber δ.toNNReal S := by
    intro S hS_nonempty hS_sub
    let K : NNReal := 2
    have h_lip_on : ∀ (x y : AffineLine), x ∈ S → y ∈ S →
        dist (f x) (f y) ≤ (K : ℝ) * dist x y := by
      intro x y hx hy
      have h := h_f_lip x y (hS_sub hx) (hS_sub hy)
      simpa [K] using h
    have h1 : Metric.externalCoveringNumber (2 * K * δ.toNNReal) (f '' S) ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
      exact @externalCoveringNumber_image_lipschitz_on AffineLine ℝ _ _ f K S δ.toNNReal hS_nonempty h_lip_on
    have hK_eq : (2 * K * δ.toNNReal : NNReal) = 4 * δ.toNNReal := by
      have hK2 : 2 * K = (4 : NNReal) := by
        apply NNReal.coe_injective
        have h : ((2 * K : NNReal) : ℝ) = 4 := by
          simp [K] <;> norm_num
        exact_mod_cast h
      rw [hK2] <;> ring
    let imgS : Set ℝ := f '' S
    let δ2 : NNReal := 2 * δ.toNNReal
    let δ4 : NNReal := 4 * δ.toNNReal
    have h2 : Metric.externalCoveringNumber δ.toNNReal imgS ≤
        2 * Metric.externalCoveringNumber δ2 imgS :=
      @real_covering_doubling imgS δ.toNNReal (by positivity)
    have h3 : Metric.externalCoveringNumber δ2 imgS ≤
        2 * Metric.externalCoveringNumber δ4 imgS := by
      have h := @real_covering_doubling imgS δ2 (by positivity)
      have h_eq : (2 * δ2 : NNReal) = δ4 := by
        simp [δ2, δ4] <;> ring
      rw [h_eq] at h
      exact h
    have h4 : Metric.externalCoveringNumber δ4 imgS ≤
        Metric.externalCoveringNumber δ.toNNReal S := by
      have h6 : δ4 = 4 * δ.toNNReal := by rfl
      have h7 : (4 * δ.toNNReal : NNReal) = 2 * K * δ.toNNReal := hK_eq.symm
      rw [h6, h7]
      exact h1
    calc Metric.externalCoveringNumber δ.toNNReal imgS
      ≤ 2 * Metric.externalCoveringNumber δ2 imgS := h2
    _ ≤ 2 * (2 * Metric.externalCoveringNumber δ4 imgS) := by gcongr
    _ = 4 * Metric.externalCoveringNumber δ4 imgS := by ring
    _ ≤ 4 * Metric.externalCoveringNumber δ.toNNReal S := by gcongr
  -- Main S-set property
  refine' ⟨hA_nonempty, hδ_pos, by positivity, hs_nonneg, _⟩
  intro x r hr
  by_cases h_nonempty : (A ∩ Metric.closedBall x r).Nonempty
  · rcases h_nonempty with ⟨a₀, ha₀⟩
    have ha₀_A : a₀ ∈ A := ha₀.1
    have ha₀_ball : a₀ ∈ Metric.closedBall x r := ha₀.2
    have h_dist_eq : ∀ (y z : ℝ), dist y z = |y - z| := by
      intro y z
      simp [dist_eq_norm, Real.norm_eq_abs] <;> rfl
    rcases ha₀_A with ⟨ℓ₀, hℓ₀_T, rfl⟩
    have h' : |f ℓ₀ - x| ≤ r := by
      have h_eq : dist (f ℓ₀) x = |f ℓ₀ - x| := h_dist_eq (f ℓ₀) x
      have h : dist (f ℓ₀) x ≤ r := ha₀_ball
      rw [h_eq] at h
      exact h
    let S : Set AffineLine := T ∩ {ℓ | |f ℓ - x| ≤ r}
    have hℓ₀_in_S : ℓ₀ ∈ S := ⟨hℓ₀_T, h'⟩
    have hS_nonempty : S.Nonempty := ⟨ℓ₀, hℓ₀_in_S⟩
    have hS_sub : S ⊆ T := by intro ℓ hℓ; exact hℓ.1
    have hS1 : A ∩ Metric.closedBall x r = f '' S := by
      ext y
      simp only [A, S, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨ℓ, hℓ, rfl⟩, hball⟩
        refine ⟨ℓ, ⟨hℓ, ?_⟩, rfl⟩
        have h : dist (f ℓ) x ≤ r := hball
        have h' : |f ℓ - x| ≤ r := by
          rw [←h_dist_eq (f ℓ) x]
          exact h
        exact h'
      · rintro ⟨ℓ, ⟨hℓ, hstrip⟩, rfl⟩
        have h : dist (f ℓ) x ≤ r := by
          rw [h_dist_eq (f ℓ) x]
          exact hstrip
        exact ⟨⟨ℓ, hℓ, rfl⟩, h⟩
    have hS2 : S ⊆ Metric.closedBall ℓ₀ (140 * r) := by
      intro ℓ hℓ
      have hℓ_T : ℓ ∈ T := hℓ.1
      have hstrip : |f ℓ - x| ≤ r := hℓ.2
      have h1_v1 := (h_slope ℓ hℓ_T).1
      have h2_v1 := (h_slope ℓ₀ hℓ₀_T).1
      have h1_s := (h_slope ℓ hℓ_T).2
      have h2_s := (h_slope ℓ₀ hℓ₀_T).2
      have h_near1 := h_near ℓ hℓ_T
      have h_near2 := h_near ℓ₀ hℓ₀_T
      have h_dist : dist ℓ ℓ₀ ≤ 60 * |f ℓ - f ℓ₀| + 20 * δ :=
        dist_bound_near_point_R2 ℓ ℓ₀ p δ hδ_pos hR hδ_le_one h_near1 h_near2 h1_v1 h2_v1 h1_s h2_s
      have h_slope_diff : |f ℓ - f ℓ₀| ≤ 2 * r := by
        have h1 : |f ℓ - f ℓ₀| ≤ |f ℓ - x| + |x - f ℓ₀| := by exact abs_sub_le (f ℓ) x (f ℓ₀)
        have h2 : |x - f ℓ₀| ≤ r := by
          have h3 : |f ℓ₀ - x| ≤ r := hℓ₀_in_S.2
          rw [show x - f ℓ₀ = -(f ℓ₀ - x) by ring]
          rw [abs_neg]
          exact h3
        linarith
      have h3 : dist ℓ ℓ₀ ≤ 140 * r := by
        calc dist ℓ ℓ₀ ≤ 60 * |f ℓ - f ℓ₀| + 20 * δ := h_dist
          _ ≤ 60 * (2 * r) + 20 * δ := by gcongr
          _ = 120 * r + 20 * δ := by ring
          _ ≤ 140 * r := by linarith [hr]
      simpa [Metric.mem_closedBall] using h3
    have hS2' : S ⊆ T ∩ Metric.closedBall ℓ₀ (140 * r) := by
      intro ℓ hℓ
      exact ⟨hℓ.1, hS2 hℓ⟩
    have hT_sset := hT.2.2.2.2
    have h4 : Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall ℓ₀ (140 * r)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (140 * r)) ^ s *
          Metric.externalCoveringNumber δ.toNNReal T :=
      hT_sset ℓ₀ (140 * r) (by linarith [hr])
    have h5 : Metric.externalCoveringNumber δ.toNNReal S ≤
        Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall ℓ₀ (140 * r)) :=
      Metric.externalCoveringNumber_mono_set hS2'
    have h6 : Metric.externalCoveringNumber δ.toNNReal (f '' S) ≤
        4 * Metric.externalCoveringNumber δ.toNNReal S :=
      h_image_bound S hS_nonempty hS_sub
    have h7 : (ENNReal.ofReal (140 * r)) ^ s ≤ ENNReal.ofReal 140 * (ENNReal.ofReal r) ^ s := by
      have hr_nonneg : 0 ≤ r := by linarith [hr]
      have h_ineq : (140 * r) ^ s ≤ 140 * r ^ s := by
        have h1 : ((140 : ℝ) * r) ^ s = (140 : ℝ) ^ s * r ^ s := by
          rw [Real.mul_rpow] <;> linarith
        rw [h1]
        have h2 : (140 : ℝ) ^ s ≤ (140 : ℝ) := by
          have h21 : (140 : ℝ) ^ s ≤ (140 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hs_le_one
          have h22 : (140 : ℝ) ^ (1 : ℝ) = (140 : ℝ) := by simp
          rw [h22] at h21
          exact h21
        have h3 : 0 ≤ r ^ s := Real.rpow_nonneg (by linarith) s
        exact mul_le_mul_of_nonneg_right h2 h3
      have h4' : ENNReal.ofReal ((140 * r) ^ s) ≤ ENNReal.ofReal (140 * r ^ s) :=
        ENNReal.ofReal_le_ofReal h_ineq
      have h5' : (ENNReal.ofReal (140 * r)) ^ s = ENNReal.ofReal ((140 * r) ^ s) :=
        ENNReal.ofReal_rpow_of_nonneg (by linarith) hs_nonneg
      have h6' : ENNReal.ofReal (140 * r ^ s) = ENNReal.ofReal 140 * (ENNReal.ofReal r) ^ s := by
        have h71 : ENNReal.ofReal (140 * r ^ s) = ENNReal.ofReal 140 * ENNReal.ofReal (r ^ s) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        rw [h71]
        have h8 : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) :=
          ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs_nonneg
        rw [h8]
      rw [h5']
      exact h4'.trans (le_of_eq h6')
    let eT : Set AffineLine → ENNReal := fun S => (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)
    let eR : Set ℝ → ENNReal := fun S => (Metric.externalCoveringNumber δ.toNNReal S : ENNReal)
    have h4' : eT (T ∩ Metric.closedBall ℓ₀ (140 * r)) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (140 * r)) ^ s * eT T := by
      dsimp only [eT]
      exact_mod_cast h4
    have h5' : eT S ≤ eT (T ∩ Metric.closedBall ℓ₀ (140 * r)) := by
      have h5_cast : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall ℓ₀ (140 * r)) : ENNReal) :=
        by exact_mod_cast h5
      simpa [eT] using h5_cast
    have h6' : eR (f '' S) ≤ (4 : ENNReal) * eT S := by
      dsimp only [eR, eT]
      have h : (Metric.externalCoveringNumber δ.toNNReal (f '' S) : ENNReal) ≤
          ((4 * Metric.externalCoveringNumber δ.toNNReal S : ℕ∞) : ENNReal) := by
        exact_mod_cast h6
      have h2 : ((4 * Metric.externalCoveringNumber δ.toNNReal S : ℕ∞) : ENNReal) =
          (4 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
        simp
      rw [h2] at h
      exact h
    have h_global' : eT T ≤ (600 : ENNReal) * eR A := by
      dsimp only [eT, eR]
      have h : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤
          ((600 * Metric.externalCoveringNumber δ.toNNReal A : ℕ∞) : ENNReal) := by
        exact_mod_cast h_global
      have h2 : ((600 * Metric.externalCoveringNumber δ.toNNReal A : ℕ∞) : ENNReal) =
          (600 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) := by
        simp
      rw [h2] at h
      exact h
    have h_mul1 : (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal 140 * (ENNReal.ofReal r) ^ s) * eT T) =
        ENNReal.ofReal (560 * C) * (ENNReal.ofReal r) ^ s * eT T := by
      have h9 : (4 : ENNReal) = ENNReal.ofReal 4 := by norm_cast
      rw [h9]
      have h_posC : 0 ≤ C := by linarith
      have h10 : ENNReal.ofReal 4 * (ENNReal.ofReal C * (ENNReal.ofReal 140 * (ENNReal.ofReal r) ^ s) * eT T) =
          (ENNReal.ofReal 4 * ENNReal.ofReal C * ENNReal.ofReal 140) * ((ENNReal.ofReal r) ^ s * eT T) := by
        simp only [mul_assoc] <;> ac_rfl
      rw [h10]
      have h11 : ENNReal.ofReal 4 * ENNReal.ofReal C * ENNReal.ofReal 140 = ENNReal.ofReal (560 * C) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num),
            ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 * C by positivity)]
        <;> norm_cast <;> ring_nf
      rw [h11] <;> ac_rfl
    have h_mul2 : ENNReal.ofReal (560 * C) * (ENNReal.ofReal r) ^ s * ((600 : ENNReal) * eR A) =
        ENNReal.ofReal (336000 * C) * (ENNReal.ofReal r) ^ s * eR A := by
      have h13 : (600 : ENNReal) = ENNReal.ofReal 600 := by norm_cast
      rw [h13]
      have h14 : ENNReal.ofReal (560 * C) * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal 600 * eR A) =
          (ENNReal.ofReal (560 * C) * ENNReal.ofReal 600) * ((ENNReal.ofReal r) ^ s * eR A) := by
        simp only [mul_assoc] <;> ac_rfl
      rw [h14]
      have h15 : ENNReal.ofReal (560 * C) * ENNReal.ofReal 600 = ENNReal.ofReal (336000 * C) := by
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 560 * C by positivity)]
        <;> norm_cast <;> ring_nf
      rw [h15] <;> ac_rfl
    calc eR (A ∩ Metric.closedBall x r)
      = eR (f '' S) := by rw [hS1]
    _ ≤ (4 : ENNReal) * eT S := h6'
    _ ≤ (4 : ENNReal) * eT (T ∩ Metric.closedBall ℓ₀ (140 * r)) := by
      exact mul_le_mul_of_nonneg_left h5' (by positivity)
    _ ≤ (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal (140 * r)) ^ s * eT T) := by
      exact mul_le_mul_of_nonneg_left h4' (by positivity)
    _ ≤ (4 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal 140 * (ENNReal.ofReal r) ^ s) * eT T) := by
      gcongr <;> exact h7
    _ = ENNReal.ofReal (560 * C) * (ENNReal.ofReal r) ^ s * eT T := h_mul1
    _ ≤ ENNReal.ofReal (560 * C) * (ENNReal.ofReal r) ^ s * ((600 : ENNReal) * eR A) := by
      gcongr <;> exact h_global'
    _ = ENNReal.ofReal (336000 * C) * (ENNReal.ofReal r) ^ s * eR A := h_mul2
    _ ≤ ENNReal.ofReal (400000 * C) * (ENNReal.ofReal r) ^ s * eR A := by
      have h336 : 336000 * C ≤ 400000 * C := by
        have hC_nonneg : 0 ≤ C := by linarith [hC_pos]
        nlinarith
      have h337 : ENNReal.ofReal (336000 * C) ≤ ENNReal.ofReal (400000 * C) := by
        gcongr <;> nlinarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h337 (by positivity)) (by positivity)
  · have h_eq : (A ∩ Metric.closedBall x r) = ∅ := by
      by_contra h
      have h' : (A ∩ Metric.closedBall x r).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr h
      exact h_nonempty h'
    rw [Metric.externalCoveringNumber_eq_zero.mpr h_eq]
    <;> simp

/-- Intercept bound for a line through the unit square with |slope| ≤ 1.

If `p ∈ [0,1)²` lies on the line `x = a*y + b` and `|a| ≤ 1`, then `|b| < 2`.
Geometrically: `b = p₀ - a*p₁`, so `-1 ≤ b < 2`. -/
lemma intercept_bound_of_unit_square {a b : ℝ} {p : Plane}
    (ha : |a| ≤ 1) (hp0 : 0 ≤ p 0) (hp0' : p 0 < 1)
    (hp1 : 0 ≤ p 1) (hp1' : p 1 < 1)
    (h_line : p 0 = a * p 1 + b) : |b| < 2 := by
  have hb_eq : b = p 0 - a * p 1 := by linarith
  have h_abs_a_le_one : |a| ≤ 1 := ha
  have h_product_lt_one : |a| * p 1 < 1 := by
    calc |a| * p 1 ≤ 1 * p 1 := by gcongr
      _ = p 1 := by ring
      _ < 1 := hp1'
  have h_product_nonneg : 0 ≤ |a| * p 1 := by positivity
  have h_upper : b < 2 := by
    rw [hb_eq]
    have h1 : -a * p 1 ≤ |a| * p 1 := by
      have h2 : -a ≤ |a| := by exact neg_le_abs a
      exact mul_le_mul_of_nonneg_right h2 hp1
    have h3 : p 0 - a * p 1 ≤ p 0 + |a| * p 1 := by
      have h4 : p 0 - a * p 1 = p 0 + (-a * p 1) := by ring
      rw [h4]; gcongr
    have h5 : p 0 + |a| * p 1 < 2 := by
      have h6 : p 0 < 1 := hp0'
      linarith
    exact lt_of_le_of_lt h3 h5
  have h_lower : -1 ≤ b := by
    rw [hb_eq]
    have h1 : a * p 1 ≤ |a| * p 1 := by
      have h2 : a ≤ |a| := by exact le_abs_self a
      exact mul_le_mul_of_nonneg_right h2 hp1
    have h3 : p 0 - a * p 1 ≥ p 0 - |a| * p 1 := by
      have h4 : p 0 - a * p 1 = p 0 - (a * p 1) := by ring
      rw [h4]; gcongr
    have h5 : p 0 - |a| * p 1 ≥ -1 := by
      have h6 : p 0 ≥ 0 := hp0
      have h7 : |a| * p 1 ≤ 1 := by linarith [h_product_lt_one]
      linarith
    exact le_trans h5 h3
  have h_abs_lower : -2 < b := by linarith
  exact abs_lt.mpr ⟨h_abs_lower, h_upper⟩

end TubesAndSlopes
