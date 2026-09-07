module

/-
  A9 Helpers: counting and bounding lemmas for A9 affine normalization.

  Extracted from A9_Helpers for compilation performance.
  Contains: AppendixA namespace (dyadic cells, packing bounds, Y regularity, etc.).
  Depends on: A9_Support
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.CoarseParamsSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A9_Support
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable


namespace DirecretisedFurstenbergEstimate

namespace AppendixA

open DirecretisedFurstenbergEstimate
open LemmaE
open DiscretisedFurstenbergEstimate.CoveringUtils
open TubesAndSlopes

/-! ========================================================================
   Helper lemmas adapted from lagoon's A9 proof
   (dyadicCellOfParams is now defined in Interfaces.lean)
   ======================================================================== -/

/-- Bound on affine projection of a point in [0,1]² with |σ| ≤ 1. -/
lemma projection_bound (p : Plane) (σ : ℝ)
    (h1 : 0 ≤ p 0) (h2 : p 0 ≤ 1) (h3 : 0 ≤ p 1) (h4 : p 1 ≤ 1)
    (hσ1 : -1 ≤ σ) (hσ2 : σ ≤ 1) :
    p 0 - σ * p 1 ∈ Set.Icc (-1 : ℝ) 2 := by
  have h_lower : -1 ≤ p 0 - σ * p 1 := by
    by_cases h : 0 ≤ σ
    · have h5 : σ * p 1 ≤ p 1 := by nlinarith
      nlinarith
    · have h5 : -σ ≤ 1 := by linarith
      nlinarith
  have h_upper : p 0 - σ * p 1 ≤ 2 := by
    by_cases h : 0 ≤ σ
    · nlinarith
    · have h5 : -σ ≤ 1 := by linarith
      nlinarith
  exact ⟨h_lower, h_upper⟩

/-- y_Q = Δ*(Q.2 + 1/2) ∈ [-2,2] if square meets ball of radius √2. -/
lemma y_Q_in_Icc2 {Δ : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (Q : CoarseSquare Δ) (p : Plane)
    (hp_in_square : p 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)))
    (hp_in_ball : ‖p‖ ≤ Real.sqrt 2) :
    Δ * ((Q.2 : ℝ) + 1 / 2) ∈ Set.Icc (-2 : ℝ) 2 := by
  have hpy1 : |p 1| ≤ Real.sqrt 2 := by
    have h : |p 1| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 1
    linarith [hp_in_ball]
  rcases hp_in_square with ⟨hlo, hhi⟩
  have h_center_diff : |Δ * ((Q.2 : ℝ) + 1 / 2) - p 1| ≤ Δ / 2 := by
    have h3 : -Δ / 2 ≤ Δ * ((Q.2 : ℝ) + 1 / 2) - p 1 := by linarith [hhi]
    have h4 : Δ * ((Q.2 : ℝ) + 1 / 2) - p 1 ≤ Δ / 2 := by linarith [hlo]
    rw [abs_le]; constructor <;> linarith
  have h5 : |Δ * ((Q.2 : ℝ) + 1 / 2)| ≤ |p 1| + Δ / 2 := by
    calc |Δ * ((Q.2 : ℝ) + 1 / 2)|
      = |p 1 + (Δ * ((Q.2 : ℝ) + 1 / 2) - p 1)| := by ring_nf
    _ ≤ |p 1| + |Δ * ((Q.2 : ℝ) + 1 / 2) - p 1| := by exact DiscretisedFurstenbergEstimate.real_abs_add (p.ofLp 1) (Δ * (↑Q.2 + 1 / 2) - p.ofLp 1)
    _ ≤ |p 1| + Δ / 2 := by gcongr
  have h6 : |Δ * ((Q.2 : ℝ) + 1 / 2)| < 2 := by
    have h7 : |p 1| + Δ / 2 ≤ Real.sqrt 2 + Δ / 2 := by linarith [hpy1]
    have h8 : Real.sqrt 2 + Δ / 2 < 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have h11 : -2 ≤ Δ * ((Q.2 : ℝ) + 1 / 2) := by linarith [abs_lt.mp h6]
  have h12 : Δ * ((Q.2 : ℝ) + 1 / 2) ≤ 2 := by linarith [abs_lt.mp h6]
  exact ⟨h11, h12⟩

/-- A bounded nonempty set is an S-set with sufficiently large constant. -/
lemma bounded_set_is_sset_of_large_constant_general
    {Δ τ C_out B : ℝ}
    (hΔ_pos : 0 < Δ)
    (hτ_pos : 0 < τ)
    (hC_out_pos : 0 < C_out)
    (hC_out_large : C_out * Real.rpow Δ τ ≥ 1)
    {Y : Set ℝ}
    (hY_nonempty : Y.Nonempty)
    (hY_bounds : Y ⊆ Set.Icc (-B) B) :
    IsDeltaSSet Δ τ C_out Y := by
  have h_main : ∀ (y : ℝ) (r : ℝ), Δ ≤ r →
      (Metric.externalCoveringNumber Δ.toNNReal (Y ∩ Metric.closedBall y r) : ℝ≥0∞) ≤
        ENNReal.ofReal C_out * (ENNReal.ofReal r) ^ τ *
          (Metric.externalCoveringNumber Δ.toNNReal Y : ℝ≥0∞) := by
    intro y r hr
    have h_r_nonneg : 0 ≤ r := by linarith
    have hτ_nonneg : 0 ≤ τ := by linarith
    have hC_out_nonneg : 0 ≤ C_out := by linarith
    have h_sub : (Y ∩ Metric.closedBall y r) ⊆ Y := Set.inter_subset_left
    have h1 : (Metric.externalCoveringNumber Δ.toNNReal (Y ∩ Metric.closedBall y r) : ℝ≥0∞) ≤
        (Metric.externalCoveringNumber Δ.toNNReal Y : ℝ≥0∞) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
    have h3 : Real.rpow Δ τ ≤ Real.rpow r τ :=
      Real.rpow_le_rpow (by linarith) (by linarith) hτ_nonneg
    have h4 : C_out * Real.rpow r τ ≥ C_out * Real.rpow Δ τ := by gcongr <;> linarith
    have h2 : C_out * Real.rpow r τ ≥ 1 := by linarith
    have h6 : ENNReal.ofReal (C_out * Real.rpow r τ) =
        ENNReal.ofReal C_out * (ENNReal.ofReal r) ^ τ := by
      have h7 : (ENNReal.ofReal r) ^ τ = ENNReal.ofReal (Real.rpow r τ) :=
        ENNReal.ofReal_rpow_of_nonneg h_r_nonneg hτ_nonneg
      rw [ENNReal.ofReal_mul hC_out_nonneg, h7]
    have h5 : ENNReal.ofReal C_out * (ENNReal.ofReal r) ^ τ ≥ 1 := by
      rw [←h6]; exact ENNReal.one_le_ofReal.mpr h2
    calc (Metric.externalCoveringNumber Δ.toNNReal (Y ∩ Metric.closedBall y r) : ℝ≥0∞)
      ≤ (Metric.externalCoveringNumber Δ.toNNReal Y : ℝ≥0∞) := h1
    _ = 1 * (Metric.externalCoveringNumber Δ.toNNReal Y : ℝ≥0∞) := by simp
    _ ≤ (ENNReal.ofReal C_out * (ENNReal.ofReal r) ^ τ) *
          (Metric.externalCoveringNumber Δ.toNNReal Y : ℝ≥0∞) := by
        gcongr <;> exact h5
  exact ⟨hY_nonempty, hΔ_pos, hC_out_pos, by linarith, h_main⟩

/-- Residual bound from cthickening: if p is within δ of line T (parameterized x = a*y + b),
    then |p 0 - a*p 1 - b| ≤ sqrt(1+a²) * δ. -/
lemma residual_from_cthickening (p : Plane) (T : AffineLine) (δ : ℝ)
    (hδ_nonneg : 0 ≤ δ)
    (hv : (LemmaE.getDirV T) 1 ≠ 0)
    (h : p ∈ Metric.cthickening δ (T.1 : Set Plane)) :
    |p 0 - tubeSlope T * p 1 - tubeIntercept T| ≤
      Real.sqrt (1 + (tubeSlope T)^2) * δ := by
  set a := tubeSlope T with ha
  set b := tubeIntercept T with hb
  let q : Plane := EuclideanGeometry.orthogonalProjection T.1 p
  have hq_mem : q ∈ T.1 := EuclideanGeometry.orthogonalProjection_mem p
  have h_line : q 0 = a * q 1 + b := LemmaE.affineLineParams_correct T hv q hq_mem
  have h_edist : Metric.infEDist p T.1 ≤ ENNReal.ofReal δ :=
    Metric.mem_cthickening_iff.mp h
  have h_dist : dist p q ≤ δ := by
    have h_eq : dist p q = Metric.infDist p T.1 :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist T.1 p
    rw [h_eq]
    have h_conv : Metric.infDist p T.1 = ENNReal.toReal (Metric.infEDist p T.1) := by rfl
    rw [h_conv]
    have h_mono : ENNReal.toReal (Metric.infEDist p T.1) ≤ ENNReal.toReal (ENNReal.ofReal δ) :=
      ENNReal.toReal_mono (by simp) h_edist
    rw [ENNReal.toReal_ofReal hδ_nonneg] at h_mono
    exact h_mono
  let n : Plane := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -a)
  have h_eq1 : p 0 - a * p 1 - b = (p - q) 0 - a * (p - q) 1 := by
    have h : q 0 = a * q 1 + b := h_line
    simp [h] <;> ring
  have h_eq2 : (p - q) 0 - a * (p - q) 1 = inner ℝ (p - q) n := by
    simp [n, inner, Fin.sum_univ_two] <;> ring
  have h_cs : |inner ℝ (p - q) n| ≤ ‖p - q‖ * ‖n‖ := by exact abs_real_inner_le_norm (p - q) n
  have h_norm_n : ‖n‖ = Real.sqrt (1 + a ^ 2) := by
    have h_pos2 : 0 ≤ (n 0) ^ 2 + (n 1) ^ 2 := by positivity
    have h21 : ‖n‖ = Real.sqrt ((n 0) ^ 2 + (n 1) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
    rw [h21]
    have h3 : (n 0) ^ 2 + (n 1) ^ 2 = 1 + a ^ 2 := by
      simp [n, Fin.sum_univ_two] <;> ring
    rw [h3]
  rw [h_eq1, h_eq2]
  have h3 : |inner ℝ (p - q) n| ≤ ‖p - q‖ * Real.sqrt (1 + a ^ 2) := by
    rw [h_norm_n] at h_cs; exact h_cs
  have h4 : ‖p - q‖ ≤ δ := h_dist
  have h5 : ‖p - q‖ * Real.sqrt (1 + a ^ 2) ≤ Real.sqrt (1 + a ^ 2) * δ := by
    have h_nonneg : 0 ≤ Real.sqrt (1 + a ^ 2) := Real.sqrt_nonneg _
    have h : ‖p - q‖ * Real.sqrt (1 + a ^ 2) ≤ δ * Real.sqrt (1 + a ^ 2) :=
      mul_le_mul_of_nonneg_right h4 h_nonneg
    have h_comm : δ * Real.sqrt (1 + a ^ 2) = Real.sqrt (1 + a ^ 2) * δ := by ring
    rw [h_comm] at h
    exact h
  exact le_trans h3 h5

/-! ========================================================================
   A9: Affine normalization with dyadic data
   ======================================================================== -/

/-- General Lipschitz bound: AffineLine distance ≤ (3+B) * parameter distance,
    where B bounds the intercept of the second line. No slope bound required. -/
lemma affineLine_antilipschitz_general {B : ℝ} (hB : 0 ≤ B)
    (ℓ₁ ℓ₂ : AffineLine)
    (hv1 : (LemmaE.getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (LemmaE.getDirV ℓ₂) 1 ≠ 0)
    (hb2 : |tubeIntercept ℓ₂| ≤ B) :
    dist ℓ₁ ℓ₂ ≤ (3 + B) * dist (tubeSlope ℓ₁, tubeIntercept ℓ₁)
      (tubeSlope ℓ₂, tubeIntercept ℓ₂) := by
  set a1 := tubeSlope ℓ₁ with ha1
  set a2 := tubeSlope ℓ₂ with ha2
  set b1 := tubeIntercept ℓ₁ with hb1
  set b2 := tubeIntercept ℓ₂ with hb2_eq
  set dp := dist (a1, b1) (a2, b2) with hdp
  have h_da : |a1 - a2| ≤ dp := by
    rw [hdp, Prod.dist_eq] <;> exact le_max_left _ _
  have h_db : |b1 - b2| ≤ dp := by
    rw [hdp, Prod.dist_eq] <;> exact le_max_right _ _
  have h_proj : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤
      2 * |a1 - a2| :=
    TubesAndSlopes.direction_proj_upper_bound ℓ₁ ℓ₂ hv1 hv2
  have h_off11 : ℓ₁.offset 0 = b1 / (1 + a1^2) :=
    (TubesAndSlopes.offset_formula ℓ₁ hv1).1
  have h_off12 : ℓ₁.offset 1 = -a1 * b1 / (1 + a1^2) :=
    (TubesAndSlopes.offset_formula ℓ₁ hv1).2
  have h_off21 : ℓ₂.offset 0 = b2 / (1 + a2^2) :=
    (TubesAndSlopes.offset_formula ℓ₂ hv2).1
  have h_off22 : ℓ₂.offset 1 = -a2 * b2 / (1 + a2^2) :=
    (TubesAndSlopes.offset_formula ℓ₂ hv2).2
  have h_off : ‖ℓ₁.offset - ℓ₂.offset‖ ≤ B * |a1 - a2| + |b1 - b2| :=
    TubesAndSlopes.offset_diff_bound_tight hb2 hB ℓ₁.offset ℓ₂.offset
      h_off11 h_off12 h_off21 h_off22
  have h_dist_def : dist ℓ₁ ℓ₂ =
      ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
      ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
  rw [h_dist_def]
  calc _
    ≤ 2 * |a1 - a2| + (B * |a1 - a2| + |b1 - b2|) := by gcongr
    _ = (2 + B) * |a1 - a2| + |b1 - b2| := by ring
    _ ≤ (2 + B) * dp + dp := by gcongr <;> linarith
    _ = (3 + B) * dp := by ring

/-- Tight antilipschitz: dist(line) ≤ 6 * dist(params) where dist on params is L∞.
    The proof of affineLineParams_antilipschitz establishes this bound. -/
lemma affineLineParams_antilipschitz_tight
    (ℓ₁ ℓ₂ : AffineLine)
    (hv1 : (getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (getDirV ℓ₂) 1 ≠ 0)
    (ha1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (ha2 : |(affineLineParams ℓ₂).1| ≤ 1)
    (hb1 : |(affineLineParams ℓ₁).2| ≤ 3)
    (hb2 : |(affineLineParams ℓ₂).2| ≤ 3) :
    dist ℓ₁ ℓ₂ ≤ 6 * dist (affineLineParams ℓ₁) (affineLineParams ℓ₂) := by
  set a1 := (affineLineParams ℓ₁).1 with ha1_def
  set a2 := (affineLineParams ℓ₂).1 with ha2_def
  set b1 := (affineLineParams ℓ₁).2 with hb1_def
  set b2 := (affineLineParams ℓ₂).2 with hb2_def
  set dp := dist (a1, b1) (a2, b2) with hdp_def
  have h_dp_def : dp = max (|a1 - a2|) (|b1 - b2|) := by
    simp [hdp_def, Prod.dist_eq] <;> rfl
  have h_da_le_dp : |a1 - a2| ≤ dp := by
    rw [h_dp_def] <;> exact le_max_left _ _
  have h_db_le_dp : |b1 - b2| ≤ dp := by
    rw [h_dp_def] <;> exact le_max_right _ _
  have h_proj : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤ 2 * |a1 - a2| :=
    TubesAndSlopes.direction_proj_upper_bound ℓ₁ ℓ₂ hv1 hv2
  have h_off11 : ℓ₁.offset 0 = b1 / (1 + a1^2) :=
    (TubesAndSlopes.offset_formula ℓ₁ hv1).1
  have h_off12 : ℓ₁.offset 1 = -a1 * b1 / (1 + a1^2) :=
    (TubesAndSlopes.offset_formula ℓ₁ hv1).2
  have h_off21 : ℓ₂.offset 0 = b2 / (1 + a2^2) :=
    (TubesAndSlopes.offset_formula ℓ₂ hv2).1
  have h_off22 : ℓ₂.offset 1 = -a2 * b2 / (1 + a2^2) :=
    (TubesAndSlopes.offset_formula ℓ₂ hv2).2
  have h_off : ‖ℓ₁.offset - ℓ₂.offset‖ ≤ 3 * |a1 - a2| + |b1 - b2| :=
    TubesAndSlopes.offset_diff_bound_tight hb2 (by linarith) ℓ₁.offset ℓ₂.offset
      h_off11 h_off12 h_off21 h_off22
  have h_main : dist ℓ₁ ℓ₂ ≤ 5 * |a1 - a2| + |b1 - b2| := by
    have h_dist : dist ℓ₁ ℓ₂ =
        ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ +
        ‖ℓ₁.offset - ℓ₂.offset‖ := by rfl
    rw [h_dist]
    linarith
  calc dist ℓ₁ ℓ₂
    ≤ 5 * |a1 - a2| + |b1 - b2| := h_main
  _ ≤ 5 * dp + dp := by gcongr <;> linarith
  _ = 6 * dp := by ring

/-- Bound on floored multiplication: |δ * ⌊x/δ⌋| ≤ |x| + δ. -/
lemma floor_mul_abs_bound {δ x : ℝ} (hδ_pos : 0 < δ) :
    |δ * ⌊x / δ⌋| ≤ |x| + δ := by
  set y : ℝ := δ * ⌊x / δ⌋ with hy_def
  have h1 : y ≤ x := by
    have h2 : (⌊x / δ⌋ : ℝ) ≤ x / δ := Int.floor_le (x / δ)
    have h3 : δ * (⌊x / δ⌋ : ℝ) ≤ δ * (x / δ) := by gcongr
    have h4 : δ * (x / δ) = x := by field_simp [hδ_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3
  have h5 : x < y + δ := by
    have h6 : x / δ < (⌊x / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (x / δ)
    have h7 : x < δ * ((⌊x / δ⌋ : ℝ) + 1) := by
      calc x = δ * (x / δ) := by field_simp [hδ_pos.ne'] <;> ring
        _ < δ * ((⌊x / δ⌋ : ℝ) + 1) := by gcongr
    have h8 : δ * ((⌊x / δ⌋ : ℝ) + 1) = y + δ := by
      simp [hy_def] <;> ring
    rw [h8] at h7
    exact h7
  by_cases hx : 0 ≤ x
  · have h9 : 0 ≤ y := by
      have h10 : 0 ≤ x / δ := by positivity
      have h11 : 0 ≤ ⌊x / δ⌋ := Int.floor_nonneg.mpr h10
      exact mul_nonneg hδ_pos.le (by exact_mod_cast h11)
    rw [abs_of_nonneg h9, abs_of_nonneg hx]
    linarith
  · have hx' : x < 0 := by linarith
    have h10 : y < 0 := by
      have h11 : x / δ < 0 := by
        exact div_neg_of_neg_of_pos hx' hδ_pos
      have h12 : (⌊x / δ⌋ : ℝ) ≤ x / δ := Int.floor_le (x / δ)
      have h13 : (⌊x / δ⌋ : ℝ) < 0 := by linarith
      have h14 : ⌊x / δ⌋ < 0 := by exact_mod_cast h13
      exact mul_neg_of_pos_of_neg hδ_pos (by exact_mod_cast h14)
    rw [abs_of_neg h10, abs_of_neg hx']
    linarith

/-- Helper: if two reals have equal floors, their distance is < 1. -/
lemma abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  let n : ℤ := ⌊x⌋
  have h1 : (n : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  have h3 : ⌊y⌋ = n := h.symm
  have h4 : (n : ℝ) ≤ y := by rw [←h3]; exact Int.floor_le y
  have h5 : y < (n : ℝ) + 1 := by rw [←h3]; exact Int.lt_floor_add_one y
  have h6 : -1 < x - y := by linarith
  have h7 : x - y < 1 := by linarith
  rw [abs_lt]; exact ⟨h6, h7⟩

/-- Helper: a value in [0, δ) scaled by 5/δ lies in [0, 5). -/
lemma scaled_in_Ico {x δ : ℝ} (hδ_pos : 0 < δ) (h : x ∈ Set.Ico 0 δ) :
    0 ≤ 5 * x / δ ∧ 5 * x / δ < 5 := by
  have h1 : 0 ≤ x := h.1
  have h2 : x < δ := h.2
  have h3 : 0 ≤ 5 * x / δ := by positivity
  have h4 : 5 * x < 5 * δ := by gcongr
  have h5 : 5 * x / δ < 5 := by
    calc 5 * x / δ
      < (5 * δ) / δ := by gcongr
    _ = 5 := by field_simp [hδ_pos.ne'] <;> ring
  exact ⟨h3, h5⟩

/-- Helper: floor of a value in [0, 5) is in Finset.Icc 0 4. -/
lemma floor_in_I5 {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 5) : ⌊x⌋ ∈ Finset.Icc (0 : ℤ) 4 := by
  have h3 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr h1
  have h4 : ⌊x⌋ < 5 := Int.floor_lt.mpr h2
  simp only [Finset.mem_Icc]
  have h4' : ⌊x⌋ ≤ 4 := by linarith
  exact ⟨by exact_mod_cast h3, h4'⟩

/-- Helper: a value in [0, δ) scaled by 6/δ lies in [0, 6). -/
lemma scaled_in_Ico6 {x δ : ℝ} (hδ_pos : 0 < δ) (h : x ∈ Set.Ico 0 δ) :
    0 ≤ 6 * x / δ ∧ 6 * x / δ < 6 := by
  have h1 : 0 ≤ x := h.1
  have h2 : x < δ := h.2
  have h3 : 0 ≤ 6 * x / δ := by positivity
  have h4 : 6 * x < 6 * δ := by gcongr
  have h5 : 6 * x / δ < 6 := by
    calc 6 * x / δ
      < (6 * δ) / δ := by gcongr
    _ = 6 := by field_simp [hδ_pos.ne'] <;> ring
  exact ⟨h3, h5⟩

/-- Helper: floor of a value in [0, 6) is in Finset.Icc 0 5. -/
lemma floor_in_I6 {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 6) : ⌊x⌋ ∈ Finset.Icc (0 : ℤ) 5 := by
  have h3 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr h1
  have h4 : ⌊x⌋ < 6 := Int.floor_lt.mpr h2
  simp only [Finset.mem_Icc]
  have h4' : ⌊x⌋ ≤ 5 := by linarith
  exact ⟨by exact_mod_cast h3, h4'⟩

/-- Helper: if floor(x/δ) = c, then x - δ*c ∈ [0, δ). -/
lemma floor_cell_coord_Ico {δ : ℝ} {c : ℤ} {x : ℝ} (hδ_pos : 0 < δ)
    (h_floor : ⌊x / δ⌋ = c) : x - δ * (c : ℝ) ∈ Set.Ico 0 δ := by
  have h_left : (c : ℝ) ≤ x / δ := by rw [←h_floor]; exact Int.floor_le (x / δ)
  have h_right : x / δ < (c : ℝ) + 1 := by rw [←h_floor]; exact Int.lt_floor_add_one (x / δ)
  have h5 : 0 ≤ x / δ - (c : ℝ) := by linarith
  have h6 : 0 ≤ δ * (x / δ - (c : ℝ)) := mul_nonneg hδ_pos.le h5
  have h7 : δ * (x / δ - (c : ℝ)) = x - δ * (c : ℝ) := by
    field_simp [hδ_pos.ne'] <;> ring
  have h8 : x / δ - (c : ℝ) < 1 := by linarith
  have h9 : δ * (x / δ - (c : ℝ)) < δ := by
    calc δ * (x / δ - (c : ℝ)) < δ * 1 := by gcongr
                     _ = δ := by ring
  have h10 : δ * (x / δ - (c : ℝ)) = x - δ * (c : ℝ) := by
    field_simp [hδ_pos.ne'] <;> ring
  exact ⟨by rw [h7] at h6; exact h6, by rw [h10] at h9; exact h9⟩

/-- Extract lemma: parameter bounds for a dyadic cell from an original fine tube.

Given T_orig within Δ of T0 in FineTube metric, the floored δ-cell representative
has |params| ≤ 9Δ. Extracted to reduce context size and avoid elaboration timeouts. -/
lemma cell_param_bounds
    (Δ δ : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1/2) (hδ_pos : 0 < δ) (hδ_eq : δ = Δ^2)
    (T0 T_orig : FineTube) (σ₀ h₀ : ℝ)
    (hT0_dirV : (getDirV T0) 1 ≠ 0)
    (hT_orig_dirV : (getDirV T_orig) 1 ≠ 0)
    (hT0_bounds : |tubeSlope T0| ≤ 1 ∧ |tubeIntercept T0| ≤ 3)
    (hT_orig_bounds : |tubeSlope T_orig| ≤ 1 ∧ |tubeIntercept T_orig| ≤ 3)
    (h_dist : dist T_orig T0 ≤ Δ)
    (hσ : σ₀ = tubeSlope T0) (hh : h₀ = tubeIntercept T0)
    (cell : DyadicTubeCell δ)
    (hcell1 : cell.1 = ⌊(tubeSlope T_orig - σ₀) / δ⌋)
    (hcell2 : cell.2 = ⌊(tubeIntercept T_orig - h₀) / δ⌋) :
    |δ * (cell.1 : ℝ)| ≤ 9 * Δ ∧ |δ * (cell.2 : ℝ)| ≤ 9 * Δ := by
  have h_transfer : dist (LemmaE.affineLineParams T_orig) (LemmaE.affineLineParams T0) ≤
      8 * dist T_orig T0 :=
    A9Support.bounded_metric_transfer T_orig T0 hT_orig_dirV hT0_dirV
      hT_orig_bounds.1 hT0_bounds.1 hT_orig_bounds.2 hT0_bounds.2
  have h9 : 8 * dist T_orig T0 ≤ 8 * Δ := by gcongr
  have h_param_dist : dist (tubeSlope T_orig, tubeIntercept T_orig)
      (tubeSlope T0, tubeIntercept T0) ≤ 8 * Δ := by
    have h_eq1 : (tubeSlope T_orig, tubeIntercept T_orig) = LemmaE.affineLineParams T_orig := by
      exact Prod.mk.eta
    have h_eq2 : (tubeSlope T0, tubeIntercept T0) = LemmaE.affineLineParams T0 := by
      exact Prod.mk.eta
    rw [h_eq1, h_eq2]
    exact le_trans h_transfer h9
  have h1 : |tubeSlope T_orig - σ₀| ≤ 8 * Δ := by
    rw [hσ]
    have h_def : dist (tubeSlope T_orig, tubeIntercept T_orig) (tubeSlope T0, tubeIntercept T0) =
        max (|tubeSlope T_orig - tubeSlope T0|) (|tubeIntercept T_orig - tubeIntercept T0|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h_def] at h_param_dist
    exact le_trans (le_max_left _ _) h_param_dist
  have h2 : |tubeIntercept T_orig - h₀| ≤ 8 * Δ := by
    rw [hh]
    have h_def : dist (tubeSlope T_orig, tubeIntercept T_orig) (tubeSlope T0, tubeIntercept T0) =
        max (|tubeSlope T_orig - tubeSlope T0|) (|tubeIntercept T_orig - tubeIntercept T0|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h_def] at h_param_dist
    exact le_trans (le_max_right _ _) h_param_dist
  have h_bound1 : |δ * (cell.1 : ℝ)| ≤ 8 * Δ + δ := by
    rw [hcell1]
    have h_floor : |δ * ⌊(tubeSlope T_orig - σ₀) / δ⌋| ≤ |tubeSlope T_orig - σ₀| + δ :=
      floor_mul_abs_bound hδ_pos
    exact le_trans h_floor (by linarith [h1])
  have h_bound2 : |δ * (cell.2 : ℝ)| ≤ 8 * Δ + δ := by
    rw [hcell2]
    have h_floor : |δ * ⌊(tubeIntercept T_orig - h₀) / δ⌋| ≤ |tubeIntercept T_orig - h₀| + δ :=
      floor_mul_abs_bound hδ_pos
    exact le_trans h_floor (by linarith [h2])
  have hδ2 : δ ≤ Δ := by
    rw [hδ_eq]
    have h1 : Δ < 1 := by
      calc Δ < 1 / 2 := hΔ_lt_half
           _ < 1 := by norm_num
    have h2 : Δ * Δ ≤ Δ * (1 : ℝ) := mul_le_mul_of_nonneg_left h1.le hΔ_pos.le
    have h3 : Δ * Δ = Δ ^ 2 := by ring
    have h4 : Δ * (1 : ℝ) = Δ := by ring
    rw [h3, h4] at h2
    exact h2
  have h_final1 : |δ * (cell.1 : ℝ)| ≤ 9 * Δ := by
    calc |δ * (cell.1 : ℝ)|
      ≤ 8 * Δ + δ := h_bound1
    _ ≤ 8 * Δ + Δ := by exact add_le_add_right hδ2 (8 * Δ)
    _ = 9 * Δ := by ring
  have h_final2 : |δ * (cell.2 : ℝ)| ≤ 9 * Δ := by
    calc |δ * (cell.2 : ℝ)|
      ≤ 8 * Δ + δ := h_bound2
    _ ≤ 8 * Δ + Δ := by exact add_le_add_right hδ2 (8 * Δ)
    _ = 9 * Δ := by ring
  exact ⟨h_final1, h_final2⟩

/-- Per-cell packing bound: each dyadic δ-cell contains at most 36 δ-separated tubes. -/
lemma cell_packing_bound
    (δ : ℝ) (hδ_pos : 0 < δ)
    (S : Finset FineTube)
    (f : FineTube → DyadicTubeCell δ)
    (σ₀ h₀ : ℝ)
    (h_sep : SeparatedAt δ (S : Set FineTube))
    (h_dir : ∀ T ∈ S, (getDirV T) 1 ≠ 0)
    (h_slope : ∀ T ∈ S, |tubeSlope T| ≤ 1)
    (h_intercept : ∀ T ∈ S, |tubeIntercept T| ≤ 3)
    (h_f_def : ∀ T ∈ S, f T = (⌊(tubeSlope T - σ₀) / δ⌋, ⌊(tubeIntercept T - h₀) / δ⌋)) :
    ∀ (c : DyadicTubeCell δ), (S.filter (fun T => f T = c)).card ≤ 36 := by
  intro c
  let S_c := S.filter (fun T => f T = c)
  let g : FineTube → ℤ × ℤ := fun T =>
    (⌊6 * ((tubeSlope T - σ₀) - δ * (c.1 : ℝ)) / δ⌋,
     ⌊6 * ((tubeIntercept T - h₀) - δ * (c.2 : ℝ)) / δ⌋)
  have h_inj : Set.InjOn g (S_c : Set FineTube) := by
    intro T1 hT1 T2 hT2 h_eq
    have hS1 : T1 ∈ S := (Finset.mem_filter.mp hT1).1
    have hS2 : T2 ∈ S := (Finset.mem_filter.mp hT2).1
    have h_dir1 := h_dir T1 hS1
    have h_dir2 := h_dir T2 hS2
    have h_b2 := h_intercept T2 hS2
    set x1 := 6 * ((tubeSlope T1 - σ₀) - δ * (c.1 : ℝ)) / δ with hx1_def
    set x2 := 6 * ((tubeSlope T2 - σ₀) - δ * (c.1 : ℝ)) / δ with hx2_def
    set y1 := 6 * ((tubeIntercept T1 - h₀) - δ * (c.2 : ℝ)) / δ with hy1_def
    set y2 := 6 * ((tubeIntercept T2 - h₀) - δ * (c.2 : ℝ)) / δ with hy2_def
    have h_floor1 : ⌊x1⌋ = ⌊x2⌋ := by
      have h : (g T1).1 = (g T2).1 := by rw [h_eq]
      exact h
    have h_floor2 : ⌊y1⌋ = ⌊y2⌋ := by
      have h : (g T1).2 = (g T2).2 := by rw [h_eq]
      exact h
    have h_dx : |x1 - x2| < 1 := abs_sub_lt_one_of_floor_eq h_floor1
    have h_dy : |y1 - y2| < 1 := abs_sub_lt_one_of_floor_eq h_floor2
    have h_pos6 : 0 < 6 / δ := by positivity
    have h_eq1 : x1 - x2 = (6 / δ) * (tubeSlope T1 - tubeSlope T2) := by
      simp [hx1_def, hx2_def] <;> field_simp [hδ_pos.ne'] <;> ring
    have h_abs : |x1 - x2| = (6 / δ) * |tubeSlope T1 - tubeSlope T2| := by
      rw [h_eq1, abs_mul, abs_of_pos h_pos6] <;> ring
    have h9 : (6 / δ) * |tubeSlope T1 - tubeSlope T2| < 1 := by
      rw [←h_abs]; exact h_dx
    have h_a_diff : |tubeSlope T1 - tubeSlope T2| < δ / 6 := by
      set a := (6 / δ) with ha_def
      set x := |tubeSlope T1 - tubeSlope T2| with hx_def
      have h9 : a * x < 1 := by simpa [ha_def, hx_def] using h9
      have h_ne : a ≠ 0 := h_pos6.ne'
      have h_eq : (a * x) / a = x := by
        have h1 : (a * x) / a = (x * a) / a := by rw [mul_comm]
        rw [h1]; simp [h_ne]
      have h_lt : (a * x) / a < (1 : ℝ) / a := div_lt_div_of_pos_right h9 h_pos6
      have h15 : (1 : ℝ) / a = δ / 6 := by
        simp only [ha_def]; field_simp [hδ_pos.ne'] <;> ring
      have h16 : (a * x) / a < δ / 6 := by rw [h15] at h_lt; exact h_lt
      rw [h_eq] at h16; exact h16
    have h_b_diff : |tubeIntercept T1 - tubeIntercept T2| < δ / 6 := by
      have h_eq2 : y1 - y2 = (6 / δ) * (tubeIntercept T1 - tubeIntercept T2) := by
        simp [hy1_def, hy2_def] <;> field_simp [hδ_pos.ne'] <;> ring
      have h_abs2 : |y1 - y2| = (6 / δ) * |tubeIntercept T1 - tubeIntercept T2| := by
        rw [h_eq2, abs_mul, abs_of_pos h_pos6] <;> ring
      have h9b : (6 / δ) * |tubeIntercept T1 - tubeIntercept T2| < 1 := by
        rw [←h_abs2]; exact h_dy
      set a := (6 / δ) with ha_def
      set x := |tubeIntercept T1 - tubeIntercept T2| with hx_def
      have h9b2 : a * x < 1 := by simpa [ha_def, hx_def] using h9b
      have h_ne : a ≠ 0 := h_pos6.ne'
      have h_eq : (a * x) / a = x := by
        have h1 : (a * x) / a = (x * a) / a := by rw [mul_comm]
        rw [h1]; simp [h_ne]
      have h_lt : (a * x) / a < (1 : ℝ) / a := div_lt_div_of_pos_right h9b2 h_pos6
      have h15 : (1 : ℝ) / a = δ / 6 := by
        simp only [ha_def]; field_simp [hδ_pos.ne'] <;> ring
      have h16 : (a * x) / a < δ / 6 := by rw [h15] at h_lt; exact h_lt
      rw [h_eq] at h16; exact h16
    have h_param_dist : dist (tubeSlope T1, tubeIntercept T1)
        (tubeSlope T2, tubeIntercept T2) < δ / 6 := by
      simp [Prod.dist_eq, max_lt_iff] <;> exact ⟨h_a_diff, h_b_diff⟩
    have h_line_dist : dist T1 T2 < δ := by
      have h_antilipschitz : dist T1 T2 ≤
          6 * dist (tubeSlope T1, tubeIntercept T1) (tubeSlope T2, tubeIntercept T2) :=
        affineLineParams_antilipschitz_tight T1 T2 h_dir1 h_dir2
          (h_slope T1 hS1) (h_slope T2 hS2) (h_intercept T1 hS1) h_b2
      calc dist T1 T2
        ≤ 6 * dist (tubeSlope T1, tubeIntercept T1) (tubeSlope T2, tubeIntercept T2) := h_antilipschitz
      _ < 6 * (δ / 6) := by gcongr
      _ = δ := by ring
    by_cases h : T1 = T2
    · exact h
    · have h_sep' : δ ≤ dist T1 T2 := h_sep hS1 hS2 h
      linarith
  let I6 : Finset ℤ := Finset.Icc 0 5
  have h_image_subset : (S_c.image g) ⊆ (I6 ×ˢ I6) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨T, hT, rfl⟩
    have hS : T ∈ S := (Finset.mem_filter.mp hT).1
    have hfc : f T = c := (Finset.mem_filter.mp hT).2
    have h_f1 : ⌊(tubeSlope T - σ₀) / δ⌋ = c.1 := by
      have h : (f T).1 = c.1 := by rw [hfc]
      have h2 : (f T).1 = ⌊(tubeSlope T - σ₀) / δ⌋ := by rw [h_f_def T hS] <;> rfl
      rw [h2] at h; exact h
    have h_f2 : ⌊(tubeIntercept T - h₀) / δ⌋ = c.2 := by
      have h : (f T).2 = c.2 := by rw [hfc]
      have h2 : (f T).2 = ⌊(tubeIntercept T - h₀) / δ⌋ := by rw [h_f_def T hS] <;> rfl
      rw [h2] at h; exact h
    have h1 : (tubeSlope T - σ₀) - δ * (c.1 : ℝ) ∈ Set.Ico 0 δ :=
      floor_cell_coord_Ico hδ_pos h_f1
    have h2 : (tubeIntercept T - h₀) - δ * (c.2 : ℝ) ∈ Set.Ico 0 δ :=
      floor_cell_coord_Ico hδ_pos h_f2
    have h3 := scaled_in_Ico6 hδ_pos h1
    have h4 := scaled_in_Ico6 hδ_pos h2
    have h5 : ⌊6 * ((tubeSlope T - σ₀) - δ * (c.1 : ℝ)) / δ⌋ ∈ I6 :=
      floor_in_I6 h3.1 h3.2
    have h6 : ⌊6 * ((tubeIntercept T - h₀) - δ * (c.2 : ℝ)) / δ⌋ ∈ I6 :=
      floor_in_I6 h4.1 h4.2
    simp only [g, Finset.mem_product] <;> exact ⟨h5, h6⟩
  have h_card : (S_c.image g).card ≤ (I6 ×ˢ I6).card := Finset.card_le_card h_image_subset
  have h_card2 : (I6 ×ˢ I6).card = 36 := by
    have h : (I6 ×ˢ I6).card = I6.card * I6.card := Finset.card_product _ _
    rw [h]
    have hI6 : I6.card = 6 := by simp [I6] <;> decide
    rw [hI6] <;> norm_num
  have h_eq_card : S_c.card = (S_c.image g).card := (Finset.card_image_of_injOn h_inj).symm
  rw [h_eq_card]
  rw [h_card2] at h_card
  exact h_card

/-- Global image lower bound: if S is δ-separated and f maps to δ-cells via floor,
    then the cell image has at least |S| / 36 elements. -/
lemma cell_image_lower
    (δ : ℝ) (hδ_pos : 0 < δ)
    (S : Finset FineTube)
    (f : FineTube → DyadicTubeCell δ)
    (σ₀ h₀ : ℝ)
    (h_sep : SeparatedAt δ (S : Set FineTube))
    (h_dir : ∀ T ∈ S, (getDirV T) 1 ≠ 0)
    (h_slope : ∀ T ∈ S, |tubeSlope T| ≤ 1)
    (h_intercept : ∀ T ∈ S, |tubeIntercept T| ≤ 3)
    (h_f_def : ∀ T ∈ S, f T = (⌊(tubeSlope T - σ₀) / δ⌋, ⌊(tubeIntercept T - h₀) / δ⌋)) :
    (S.card : ℝ) ≤ 36 * (S.image f).card := by
  have h_fiber : ∀ c ∈ S.image f, (S.filter (fun T => f T = c)).card ≤ 36 :=
    fun c _ => cell_packing_bound δ hδ_pos S f σ₀ h₀ h_sep h_dir h_slope h_intercept h_f_def c
  have h_main : S.card ≤ 36 * (S.image f).card :=
    Finset.card_le_mul_card_image S 36 h_fiber
  exact_mod_cast h_main

/-- Helper: scale x ∈ [0, δ) to [0, 10). -/
lemma scaled_in_Ico10 {x δ : ℝ} (hδ_pos : 0 < δ) (h : x ∈ Set.Ico 0 δ) :
    0 ≤ 10 * x / δ ∧ 10 * x / δ < 10 := by
  have h1 : 0 ≤ x := h.1
  have h2 : x < δ := h.2
  have h3 : 0 ≤ 10 * x / δ := by positivity
  have h4 : 10 * x < 10 * δ := by gcongr
  have h5 : 10 * x / δ < 10 := by
    calc 10 * x / δ
      < (10 * δ) / δ := by gcongr
    _ = 10 := by field_simp [hδ_pos.ne'] <;> ring
  exact ⟨h3, h5⟩

/-- Helper: floor of a value in [0, 10) is in Finset.Icc 0 9. -/
lemma floor_in_I10 {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 10) : ⌊x⌋ ∈ Finset.Icc (0 : ℤ) 9 := by
  have h3 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr h1
  have h4 : ⌊x⌋ < 10 := Int.floor_lt.mpr h2
  simp only [Finset.mem_Icc]
  have h4' : ⌊x⌋ ≤ 9 := by linarith
  exact ⟨by exact_mod_cast h3, h4'⟩

/-- Helper: a value in [0, δ) scaled by 12/δ lies in [0, 12). -/
lemma scaled_in_Ico12 {x δ : ℝ} (hδ_pos : 0 < δ) (h : x ∈ Set.Ico 0 δ) :
    0 ≤ 12 * x / δ ∧ 12 * x / δ < 12 := by
  have h1 : 0 ≤ x := h.1
  have h2 : x < δ := h.2
  have h3 : 0 ≤ 12 * x / δ := by positivity
  have h4 : 12 * x < 12 * δ := by gcongr
  have h5 : 12 * x / δ < 12 := by
    calc 12 * x / δ
      < (12 * δ) / δ := by gcongr
    _ = 12 := by field_simp [hδ_pos.ne'] <;> ring
  exact ⟨h3, h5⟩

/-- Helper: floor of a value in [0, 12) is in Finset.Icc 0 11. -/
lemma floor_in_I12 {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 12) : ⌊x⌋ ∈ Finset.Icc (0 : ℤ) 11 := by
  have h3 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr h1
  have h4 : ⌊x⌋ < 12 := Int.floor_lt.mpr h2
  simp only [Finset.mem_Icc]
  have h4' : ⌊x⌋ ≤ 11 := by linarith
  exact ⟨by exact_mod_cast h3, h4'⟩

/-- Cell packing bound with half-separation.
    If S is (δ/2)-separated, each dyadic δ-cell contains at most 144 tubes. -/
lemma cell_packing_bound_half
    (δ : ℝ) (hδ_pos : 0 < δ)
    (S : Finset FineTube)
    (f : FineTube → DyadicTubeCell δ)
    (σ₀ h₀ : ℝ)
    (h_sep : SeparatedAt (δ / 2) (S : Set FineTube))
    (h_dir : ∀ T ∈ S, (getDirV T) 1 ≠ 0)
    (h_slope : ∀ T ∈ S, |tubeSlope T| ≤ 1)
    (h_intercept : ∀ T ∈ S, |tubeIntercept T| ≤ 3)
    (h_f_def : ∀ T ∈ S, f T = (⌊(tubeSlope T - σ₀) / δ⌋, ⌊(tubeIntercept T - h₀) / δ⌋)) :
    ∀ (c : DyadicTubeCell δ), (S.filter (fun T => f T = c)).card ≤ 144 := by
  intro c
  let S_c := S.filter (fun T => f T = c)
  let g : FineTube → ℤ × ℤ := fun T =>
    (⌊12 * ((tubeSlope T - σ₀) - δ * (c.1 : ℝ)) / δ⌋,
     ⌊12 * ((tubeIntercept T - h₀) - δ * (c.2 : ℝ)) / δ⌋)
  have h_inj : Set.InjOn g (S_c : Set FineTube) := by
    intro T1 hT1 T2 hT2 h_eq
    have hS1 : T1 ∈ S := (Finset.mem_filter.mp hT1).1
    have hS2 : T2 ∈ S := (Finset.mem_filter.mp hT2).1
    have h_dir1 := h_dir T1 hS1
    have h_dir2 := h_dir T2 hS2
    have h_b2 := h_intercept T2 hS2
    set x1 := 12 * ((tubeSlope T1 - σ₀) - δ * (c.1 : ℝ)) / δ with hx1_def
    set x2 := 12 * ((tubeSlope T2 - σ₀) - δ * (c.1 : ℝ)) / δ with hx2_def
    set y1 := 12 * ((tubeIntercept T1 - h₀) - δ * (c.2 : ℝ)) / δ with hy1_def
    set y2 := 12 * ((tubeIntercept T2 - h₀) - δ * (c.2 : ℝ)) / δ with hy2_def
    have h_floor1 : ⌊x1⌋ = ⌊x2⌋ := by
      have h : (g T1).1 = (g T2).1 := by rw [h_eq]
      exact h
    have h_floor2 : ⌊y1⌋ = ⌊y2⌋ := by
      have h : (g T1).2 = (g T2).2 := by rw [h_eq]
      exact h
    have h_dx : |x1 - x2| < 1 := abs_sub_lt_one_of_floor_eq h_floor1
    have h_dy : |y1 - y2| < 1 := abs_sub_lt_one_of_floor_eq h_floor2
    have h_pos12 : 0 < 12 / δ := by positivity
    have h_eq1 : x1 - x2 = (12 / δ) * (tubeSlope T1 - tubeSlope T2) := by
      simp [hx1_def, hx2_def] <;> field_simp [hδ_pos.ne'] <;> ring
    have h_abs : |x1 - x2| = (12 / δ) * |tubeSlope T1 - tubeSlope T2| := by
      rw [h_eq1, abs_mul, abs_of_pos h_pos12] <;> ring
    have h9 : (12 / δ) * |tubeSlope T1 - tubeSlope T2| < 1 := by
      rw [←h_abs]; exact h_dx
    have h_a_diff : |tubeSlope T1 - tubeSlope T2| < δ / 12 := by
      set a := (12 / δ) with ha_def
      set x := |tubeSlope T1 - tubeSlope T2| with hx_def
      have h9 : a * x < 1 := by simpa [ha_def, hx_def] using h9
      have h_ne : a ≠ 0 := h_pos12.ne'
      have h_eq : (a * x) / a = x := by
        have h1 : (a * x) / a = (x * a) / a := by rw [mul_comm]
        rw [h1]; simp [h_ne]
      have h_lt : (a * x) / a < (1 : ℝ) / a := div_lt_div_of_pos_right h9 h_pos12
      have h15 : (1 : ℝ) / a = δ / 12 := by
        simp only [ha_def]; field_simp [hδ_pos.ne'] <;> ring
      have h16 : (a * x) / a < δ / 12 := by rw [h15] at h_lt; exact h_lt
      rw [h_eq] at h16; exact h16
    have h_b_diff : |tubeIntercept T1 - tubeIntercept T2| < δ / 12 := by
      have h_eq2 : y1 - y2 = (12 / δ) * (tubeIntercept T1 - tubeIntercept T2) := by
        simp [hy1_def, hy2_def] <;> field_simp [hδ_pos.ne'] <;> ring
      have h_abs2 : |y1 - y2| = (12 / δ) * |tubeIntercept T1 - tubeIntercept T2| := by
        rw [h_eq2, abs_mul, abs_of_pos h_pos12] <;> ring
      have h9b : (12 / δ) * |tubeIntercept T1 - tubeIntercept T2| < 1 := by
        rw [←h_abs2]; exact h_dy
      set a := (12 / δ) with ha_def
      set x := |tubeIntercept T1 - tubeIntercept T2| with hx_def
      have h9b2 : a * x < 1 := by simpa [ha_def, hx_def] using h9b
      have h_ne : a ≠ 0 := h_pos12.ne'
      have h_eq : (a * x) / a = x := by
        have h1 : (a * x) / a = (x * a) / a := by rw [mul_comm]
        rw [h1]; simp [h_ne]
      have h_lt : (a * x) / a < (1 : ℝ) / a := div_lt_div_of_pos_right h9b2 h_pos12
      have h15 : (1 : ℝ) / a = δ / 12 := by
        simp only [ha_def]; field_simp [hδ_pos.ne'] <;> ring
      have h16 : (a * x) / a < δ / 12 := by rw [h15] at h_lt; exact h_lt
      rw [h_eq] at h16; exact h16
    have h_param_dist : dist (tubeSlope T1, tubeIntercept T1)
        (tubeSlope T2, tubeIntercept T2) < δ / 12 := by
      simp [Prod.dist_eq, max_lt_iff] <;> exact ⟨h_a_diff, h_b_diff⟩
    have h_line_dist : dist T1 T2 < δ / 2 := by
      have h_antilipschitz : dist T1 T2 ≤
          6 * dist (tubeSlope T1, tubeIntercept T1) (tubeSlope T2, tubeIntercept T2) :=
        affineLineParams_antilipschitz_tight T1 T2 h_dir1 h_dir2
          (h_slope T1 hS1) (h_slope T2 hS2) (h_intercept T1 hS1) h_b2
      calc dist T1 T2
        ≤ 6 * dist (tubeSlope T1, tubeIntercept T1) (tubeSlope T2, tubeIntercept T2) := h_antilipschitz
      _ < 6 * (δ / 12) := by gcongr
      _ = δ / 2 := by ring
    by_cases h : T1 = T2
    · exact h
    · have h_sep' : (δ / 2 : ℝ) ≤ dist T1 T2 := h_sep hS1 hS2 h
      linarith
  let I12 : Finset ℤ := Finset.Icc 0 11
  have h_image_subset : (S_c.image g) ⊆ (I12 ×ˢ I12) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨T, hT, rfl⟩
    have hS : T ∈ S := (Finset.mem_filter.mp hT).1
    have hfc : f T = c := (Finset.mem_filter.mp hT).2
    have h_f1 : ⌊(tubeSlope T - σ₀) / δ⌋ = c.1 := by
      have h : (f T).1 = c.1 := by rw [hfc]
      have h2 : (f T).1 = ⌊(tubeSlope T - σ₀) / δ⌋ := by rw [h_f_def T hS] <;> rfl
      rw [h2] at h; exact h
    have h_f2 : ⌊(tubeIntercept T - h₀) / δ⌋ = c.2 := by
      have h : (f T).2 = c.2 := by rw [hfc]
      have h2 : (f T).2 = ⌊(tubeIntercept T - h₀) / δ⌋ := by rw [h_f_def T hS] <;> rfl
      rw [h2] at h; exact h
    have h1 : (tubeSlope T - σ₀) - δ * (c.1 : ℝ) ∈ Set.Ico 0 δ :=
      floor_cell_coord_Ico hδ_pos h_f1
    have h2 : (tubeIntercept T - h₀) - δ * (c.2 : ℝ) ∈ Set.Ico 0 δ :=
      floor_cell_coord_Ico hδ_pos h_f2
    have h3 := scaled_in_Ico12 hδ_pos h1
    have h4 := scaled_in_Ico12 hδ_pos h2
    have h5 : ⌊12 * ((tubeSlope T - σ₀) - δ * (c.1 : ℝ)) / δ⌋ ∈ I12 :=
      floor_in_I12 h3.1 h3.2
    have h6 : ⌊12 * ((tubeIntercept T - h₀) - δ * (c.2 : ℝ)) / δ⌋ ∈ I12 :=
      floor_in_I12 h4.1 h4.2
    simp only [g, Finset.mem_product] <;> exact ⟨h5, h6⟩
  have h_card : (S_c.image g).card ≤ (I12 ×ˢ I12).card := Finset.card_le_card h_image_subset
  have h_card2 : (I12 ×ˢ I12).card = 144 := by
    have h : (I12 ×ˢ I12).card = I12.card * I12.card := Finset.card_product _ _
    rw [h]
    have hI12 : I12.card = 12 := by simp [I12] <;> decide
    rw [hI12] <;> norm_num
  have h_eq_card : S_c.card = (S_c.image g).card := (Finset.card_image_of_injOn h_inj).symm
  rw [h_eq_card]
  rw [h_card2] at h_card
  exact h_card

/-- Global image lower bound with half-separation: if S is (δ/2)-separated and f maps
    to δ-cells via floor, then the cell image has at least |S| / 144 elements. -/
lemma cell_image_lower_half
    (δ : ℝ) (hδ_pos : 0 < δ)
    (S : Finset FineTube)
    (f : FineTube → DyadicTubeCell δ)
    (σ₀ h₀ : ℝ)
    (h_sep : SeparatedAt (δ / 2) (S : Set FineTube))
    (h_dir : ∀ T ∈ S, (getDirV T) 1 ≠ 0)
    (h_slope : ∀ T ∈ S, |tubeSlope T| ≤ 1)
    (h_intercept : ∀ T ∈ S, |tubeIntercept T| ≤ 3)
    (h_f_def : ∀ T ∈ S, f T = (⌊(tubeSlope T - σ₀) / δ⌋, ⌊(tubeIntercept T - h₀) / δ⌋)) :
    (S.card : ℝ) ≤ 144 * (S.image f).card := by
  have h_fiber : ∀ c ∈ S.image f, (S.filter (fun T => f T = c)).card ≤ 144 :=
    fun c _ => cell_packing_bound_half δ hδ_pos S f σ₀ h₀ h_sep h_dir h_slope h_intercept h_f_def c
  have h_main : S.card ≤ 144 * (S.image f).card :=
    Finset.card_le_mul_card_image S 144 h_fiber
  exact_mod_cast h_main

/-- Grid covering bound for fine tubes near the origin.

    If every tube in `U` has `|slope| ≤ 7Δ`, `|intercept| ≤ 7Δ`, and nonzero
    y-direction, then `U` can be Δ-covered by 99² = 9801 grid tubes. -/
lemma A9_total_fine_upper_grid
    (Δ : ℝ)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_half : Δ < 1 / 2)
    (U : Set FineTube)
    (h_param_bounds : ∀ T ∈ U, |tubeSlope T| ≤ 7 * Δ ∧ |tubeIntercept T| ≤ 7 * Δ)
    (h_v1 : ∀ T ∈ U, (LemmaE.getDirV T) 1 ≠ 0) :
    Metric.externalCoveringNumber Δ.toNNReal U ≤ ↑(9801 : ℕ) := by
  let step : ℝ := Δ / 7
  have hstep_pos : 0 < step := by positivity
  let I : Finset ℤ := Finset.Icc (-49) 49
  let S_idx : Set (ℤ × ℤ) := ↑(I ×ˢ I)
  let f_grid : ℤ × ℤ → FineTube := fun p =>
    makeAffineLine ((p.1 : ℝ) * step) ((p.2 : ℝ) * step)
  let C_cover : Set FineTube := f_grid '' S_idx

  have h_cover : ∀ T ∈ U, ∃ C ∈ C_cover, edist T C ≤ ↑Δ.toNNReal := by
    intro T hT
    set a := tubeSlope T with ha_def
    set b := tubeIntercept T with hb_def
    have hbounds := h_param_bounds T hT
    have ha : |a| ≤ 7 * Δ := hbounds.1
    have hbb : |b| ≤ 7 * Δ := hbounds.2
    let i : ℤ := Int.floor (a / step)
    let j : ℤ := Int.floor (b / step)

    have hi1 : -49 ≤ i := by
      have h2 : (↑(-49) : ℝ) ≤ a / step := by
        have h4 : (-7 * Δ) / step = -49 := by
          simp [step] <;> field_simp [hstep_pos.ne'] <;> ring
        have h5 : -7 * Δ ≤ a := by linarith [abs_le.mp ha]
        have h6 : (-7 * Δ) / step ≤ a / step := by gcongr
        rw [h4] at h6; exact h6
      have h_mono : Int.floor ((-49 : ℝ)) ≤ Int.floor (a / step) := Int.floor_mono h2
      have h_eq : Int.floor ((-49 : ℝ)) = -49 := by
        rw [Int.floor_eq_iff] <;> norm_num
      rw [h_eq] at h_mono; exact h_mono

    have hi2 : i ≤ 49 := by
      have h2 : a / step ≤ (49 : ℝ) := by
        have h4 : (7 * Δ) / step = 49 := by
          simp [step] <;> field_simp [hstep_pos.ne'] <;> ring
        have h5 : a ≤ 7 * Δ := (abs_le.mp ha).2
        have h6 : a / step ≤ (7 * Δ) / step := by gcongr
        rw [h4] at h6; exact h6
      have h5 : (i : ℝ) ≤ a / step := Int.floor_le _
      have h6 : (i : ℝ) ≤ (49 : ℝ) := by linarith
      exact_mod_cast h6

    have hi : i ∈ I := by
      simp only [I, Finset.mem_Icc] <;> exact ⟨hi1, hi2⟩

    have hj1 : -49 ≤ j := by
      have h2 : (↑(-49) : ℝ) ≤ b / step := by
        have h4 : (-7 * Δ) / step = -49 := by
          simp [step] <;> field_simp [hstep_pos.ne'] <;> ring
        have h5 : -7 * Δ ≤ b := by linarith [abs_le.mp hbb]
        have h6 : (-7 * Δ) / step ≤ b / step := by gcongr
        rw [h4] at h6; exact h6
      have h_mono : Int.floor ((-49 : ℝ)) ≤ Int.floor (b / step) := Int.floor_mono h2
      have h_eq : Int.floor ((-49 : ℝ)) = -49 := by
        rw [Int.floor_eq_iff] <;> norm_num
      rw [h_eq] at h_mono; exact h_mono

    have hj2 : j ≤ 49 := by
      have h2 : b / step ≤ (49 : ℝ) := by
        have h4 : (7 * Δ) / step = 49 := by
          simp [step] <;> field_simp [hstep_pos.ne'] <;> ring
        have h5 : b ≤ 7 * Δ := (abs_le.mp hbb).2
        have h6 : b / step ≤ (7 * Δ) / step := by gcongr
        rw [h4] at h6; exact h6
      have h5 : (j : ℝ) ≤ b / step := Int.floor_le _
      have h6 : (j : ℝ) ≤ (49 : ℝ) := by linarith
      exact_mod_cast h6

    have hj : j ∈ I := by
      simp only [I, Finset.mem_Icc] <;> exact ⟨hj1, hj2⟩

    have h1 : |a - (i : ℝ) * step| < step := by
      have h_floor : (i : ℝ) ≤ a / step := Int.floor_le _
      have h_lt : a / step < (i : ℝ) + 1 := Int.lt_floor_add_one _
      have h9 : (i : ℝ) * step ≤ a := by
        calc (i : ℝ) * step
          = step * (i : ℝ) := by ring
        _ ≤ step * (a / step) := by gcongr
        _ = a := by field_simp [hstep_pos.ne'] <;> ring
      have h10 : a < ((i : ℝ) + 1) * step := by
        calc a
          = step * (a / step) := by field_simp [hstep_pos.ne'] <;> ring
        _ < step * ((i : ℝ) + 1) := by gcongr
        _ = ((i : ℝ) + 1) * step := by ring
      have h11 : 0 ≤ a - (i : ℝ) * step := by linarith
      rw [abs_of_nonneg h11]; linarith

    have h2 : |b - (j : ℝ) * step| < step := by
      have h_floor : (j : ℝ) ≤ b / step := Int.floor_le _
      have h_lt : b / step < (j : ℝ) + 1 := Int.lt_floor_add_one _
      have h9 : (j : ℝ) * step ≤ b := by
        calc (j : ℝ) * step
          = step * (j : ℝ) := by ring
        _ ≤ step * (b / step) := by gcongr
        _ = b := by field_simp [hstep_pos.ne'] <;> ring
      have h10 : b < ((j : ℝ) + 1) * step := by
        calc b
          = step * (b / step) := by field_simp [hstep_pos.ne'] <;> ring
        _ < step * ((j : ℝ) + 1) := by gcongr
        _ = ((j : ℝ) + 1) * step := by ring
      have h11 : 0 ≤ b - (j : ℝ) * step := by linarith
      rw [abs_of_nonneg h11]; linarith

    let p_idx : ℤ × ℤ := (i, j)
    have hp_idx : p_idx ∈ S_idx := by
      simp only [S_idx, Finset.mem_coe, Finset.mem_product]
      exact ⟨hi, hj⟩
    let C := makeAffineLine ((i : ℝ) * step) ((j : ℝ) * step)
    have hC_eq : C = f_grid p_idx := by
      have h : f_grid p_idx = makeAffineLine ((p_idx.1 : ℝ) * step) ((p_idx.2 : ℝ) * step) := by rfl
      rw [h] <;> simp [p_idx] <;> rfl
    have hC_in : C ∈ C_cover := by
      rw [hC_eq]
      exact ⟨p_idx, hp_idx, rfl⟩

    have hT_v1 : (LemmaE.getDirV T) 1 ≠ 0 := h_v1 T hT
    have hC_v1 : (LemmaE.getDirV C) 1 ≠ 0 := makeAffineLine_v1 _ _

    have h_j_abs : |(j : ℝ)| ≤ 49 := by
      have h9 : -49 ≤ j := hj1
      have h10 : j ≤ 49 := hj2
      have h11 : -49 ≤ (j : ℝ) := by exact_mod_cast h9
      have h12 : (j : ℝ) ≤ 49 := by exact_mod_cast h10
      exact abs_le.mpr ⟨h11, h12⟩

    have hC_intercept : |tubeIntercept C| ≤ 4 := by
      have h_eq : tubeIntercept C = (j : ℝ) * step := by
        have h_params : affineLineParams C = ((i : ℝ) * step, (j : ℝ) * step) := by
          rw [makeAffineLine_params]
        have h : (affineLineParams C).2 = tubeIntercept C := by rfl
        rw [h_params] at h; exact h.symm
      rw [h_eq]
      have h_abs : |(j : ℝ) * step| = |(j : ℝ)| * step := by
        calc |(j : ℝ) * step|
          = |(j : ℝ)| * |step| := by rw [abs_mul]
        _ = |(j : ℝ)| * step := by rw [abs_of_pos hstep_pos]
      rw [h_abs]
      have h10 : |(j : ℝ)| * step ≤ 49 * step := by gcongr
      have h11 : 49 * step ≤ 4 := by
        have h12 : 49 * step = 7 * Δ := by
          simp [step] <;> ring
        rw [h12]
        have h13 : 7 * Δ < 4 := by linarith
        exact h13.le
      linarith

    have h_aT : (affineLineParams T).1 = a := by rfl
    have h_bT : (affineLineParams T).2 = b := by rfl
    have h_aC : (affineLineParams C).1 = (i : ℝ) * step := by
      rw [makeAffineLine_params] <;> rfl
    have h_bC : (affineLineParams C).2 = (j : ℝ) * step := by
      rw [makeAffineLine_params] <;> rfl

    have h_dist : dist T C ≤ (2 + 4) * |a - (i : ℝ) * step| + |b - (j : ℝ) * step| := by
      have h := TubesAndSlopes.dist_bound_general T C hT_v1 hC_v1 (by norm_num) hC_intercept
      rw [h_aT, h_bT, h_aC, h_bC] at h
      exact h

    have h_final : dist T C < Δ := by
      calc dist T C
        ≤ (2 + 4) * |a - (i : ℝ) * step| + |b - (j : ℝ) * step| := h_dist
      _ = 6 * |a - (i : ℝ) * step| + |b - (j : ℝ) * step| := by norm_num
      _ < 6 * step + step := by gcongr <;> linarith
      _ = Δ := by simp [step] <;> ring

    have h_edist : edist T C ≤ ↑Δ.toNNReal := by
      rw [edist_dist]
      have h3 : (Δ.toNNReal : ℝ) = Δ := by
        rw [Real.coe_toNNReal] <;> linarith
      have h4 : dist T C ≤ (Δ.toNNReal : ℝ) := by
        rw [h3]
        exact le_of_lt h_final
      exact_mod_cast h4

    exact ⟨C, hC_in, h_edist⟩

  have h_is_cover : Metric.IsCover Δ.toNNReal U C_cover := by
    intro T hT
    exact h_cover T hT

  have h : Metric.externalCoveringNumber Δ.toNNReal U ≤ C_cover.encard :=
    h_is_cover.externalCoveringNumber_le_encard

  have h_encard_img : C_cover.encard ≤ S_idx.encard := Set.encard_image_le f_grid S_idx

  have h_encard_idx : S_idx.encard ≤ ↑(9801 : ℕ) := by
    rw [Set.encard_le_coe_iff_finite_ncard_le]
    constructor
    · exact Finset.finite_toSet (I ×ˢ I)
    · have h4 : S_idx.ncard = (I ×ˢ I).card := Set.ncard_coe_finset (I ×ˢ I)
      rw [h4]
      have hI : I.card = 99 := by decide
      rw [Finset.card_product, hI] <;> norm_num

  exact le_trans h (le_trans h_encard_img h_encard_idx)

/-- Full A9 upper bound: covering number < Δ^{-2s-ε}. -/
lemma A9_total_fine_upper
    (Δ s ε : ℝ)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_half : Δ < 1 / 2)
    (hΔ_cover : (10000 : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    (U : Set FineTube)
    (h_param_bounds : ∀ T ∈ U, |tubeSlope T| ≤ 7 * Δ ∧ |tubeIntercept T| ≤ 7 * Δ)
    (h_v1 : ∀ T ∈ U, (LemmaE.getDirV T) 1 ≠ 0) :
    Metric.externalCoveringNumber Δ.toNNReal U < ENNReal.ofReal (Real.rpow Δ (-2 * s - ε)) := by
  have h_grid : Metric.externalCoveringNumber Δ.toNNReal U ≤ ↑(9801 : ℕ) :=
    A9_total_fine_upper_grid Δ hΔ_pos hΔ_lt_half U h_param_bounds h_v1
  have h2 : (9801 : ℝ) < Real.rpow Δ (-2 * s - ε) := by
    have h1 : (9801 : ℝ) < (10000 : ℝ) := by norm_num
    linarith
  have h_pos_rpow : 0 < Real.rpow Δ (-2 * s - ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_lt_ennreal : (↑(9801 : ℕ) : ENNReal) < ENNReal.ofReal (Real.rpow Δ (-2 * s - ε)) := by
    have h_eq : (↑(9801 : ℕ) : ENNReal) = ENNReal.ofReal (9801 : ℝ) := by
      norm_cast
    rw [h_eq]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr h2
  have h_coe : (Metric.externalCoveringNumber Δ.toNNReal U : ENNReal) ≤ (↑(9801 : ℕ) : ENNReal) := by
    exact_mod_cast h_grid
  have h_final : (Metric.externalCoveringNumber Δ.toNNReal U : ENNReal) < ENNReal.ofReal (Real.rpow Δ (-2 * s - ε)) :=
    lt_of_le_of_lt h_coe h_lt_ennreal
  exact_mod_cast h_final

/- Residual bound: if p is within δ of line T (x = a*y + b), then
    |p 0 - a * p 1 - b| ≤ sqrt(1+a²) * δ. -/
lemma residual_from_cthickening_local (p : Plane) (T : AffineLine) (δ : ℝ)
    (hδ_nonneg : 0 ≤ δ)
    (hv : (LemmaE.getDirV T) 1 ≠ 0)
    (h : p ∈ Metric.cthickening δ (T.1 : Set Plane)) :
    |p 0 - tubeSlope T * p 1 - tubeIntercept T| ≤
      Real.sqrt (1 + (tubeSlope T)^2) * δ := by
  set a := tubeSlope T with ha
  set b := tubeIntercept T with hb
  let q : Plane := EuclideanGeometry.orthogonalProjection T.1 p
  have hq_mem : q ∈ T.1 := EuclideanGeometry.orthogonalProjection_mem p
  have h_line : q 0 = a * q 1 + b := LemmaE.affineLineParams_correct T hv q hq_mem
  have h_edist : Metric.infEDist p T.1 ≤ ENNReal.ofReal δ :=
    Metric.mem_cthickening_iff.mp h
  have h_dist : dist p q ≤ δ := by
    have h_eq : dist p q = Metric.infDist p T.1 :=
      EuclideanGeometry.dist_orthogonalProjection_eq_infDist T.1 p
    rw [h_eq]
    have h_conv : Metric.infDist p T.1 = ENNReal.toReal (Metric.infEDist p T.1) := by rfl
    rw [h_conv]
    have h_mono : ENNReal.toReal (Metric.infEDist p T.1) ≤ ENNReal.toReal (ENNReal.ofReal δ) :=
      ENNReal.toReal_mono (by simp) h_edist
    rw [ENNReal.toReal_ofReal hδ_nonneg] at h_mono
    exact h_mono
  let n : Plane := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (1 : ℝ) else -a)
  have h_eq1 : p 0 - a * p 1 - b = (p - q) 0 - a * (p - q) 1 := by
    have h : q 0 = a * q 1 + b := h_line
    simp [h] <;> ring
  have h_eq2 : (p - q) 0 - a * (p - q) 1 = inner ℝ (p - q) n := by
    simp [n, inner, Fin.sum_univ_two] <;> ring
  have h_cs : |inner ℝ (p - q) n| ≤ ‖p - q‖ * ‖n‖ := by exact abs_real_inner_le_norm (p - q) n
  have h_norm_n : ‖n‖ = Real.sqrt (1 + a ^ 2) := by
    have h_pos2 : 0 ≤ (n 0) ^ 2 + (n 1) ^ 2 := by positivity
    have h21 : ‖n‖ = Real.sqrt ((n 0) ^ 2 + (n 1) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
    rw [h21]
    have h22 : (n 0) ^ 2 + (n 1) ^ 2 = 1 + a ^ 2 := by
      simp [n, Fin.sum_univ_two] <;> ring
    rw [h22]
  rw [h_eq1, h_eq2]
  have h_final : |inner ℝ (p - q) n| ≤ ‖p - q‖ * Real.sqrt (1 + a ^ 2) := by
    rw [h_norm_n] at h_cs <;> exact h_cs
  have h_sqrt_nonneg : 0 ≤ Real.sqrt (1 + a ^ 2) := by positivity
  have h_last : ‖p - q‖ * Real.sqrt (1 + a ^ 2) ≤ Real.sqrt (1 + a ^ 2) * δ := by
    have h1 : ‖p - q‖ ≤ δ := h_dist
    have h2 : ‖p - q‖ * Real.sqrt (1 + a ^ 2) ≤ δ * Real.sqrt (1 + a ^ 2) :=
      mul_le_mul_of_nonneg_right h1 h_sqrt_nonneg
    have h3 : δ * Real.sqrt (1 + a ^ 2) = Real.sqrt (1 + a ^ 2) * δ := by ring
    rw [h3] at h2
    exact h2
  exact h_final.trans h_last

/-- Single-square near condition: center of Q is within 44Δ horizontal deviation
    from T0's line x = a0*y + b0. -/
lemma center_near_T0
    (Δ δ : ℝ) (hΔ_pos : 0 < Δ) (hδ_eq : δ = Δ ^ 2) (hΔ_le_half : Δ ≤ 1 / 2)
    (T0 T : FineTube)
    (a0 b0 : ℝ) (ha0_eq : a0 = tubeSlope T0) (hb0_eq : b0 = tubeIntercept T0)
    (ha0_bound : |a0| ≤ 1) (hb0_bound : |b0| ≤ 3)
    (hT0_dirV : (LemmaE.getDirV T0) 1 ≠ 0)
    (hT_dirV : (LemmaE.getDirV T) 1 ≠ 0)
    (hT_slope_bound : |tubeSlope T| ≤ 1)
    (hT_intercept_bound : |tubeIntercept T| ≤ 3)
    (Q : CoarseSquare Δ)
    (p_orig : Plane)
    (hp_near_square : p_orig ∈ Metric.cthickening (2 * Δ) (squareSet Δ Q))
    (hp_on_T : p_orig ∈ Metric.cthickening (2 * δ) (T.1 : Set Plane))
    (hT_in_T0 : InCoarseTube Δ T T0)
    (hy_Q_bounds : squareY Δ Q ∈ Set.Icc (-2 : ℝ) 2) :
    |Δ * ((Q.1 : ℝ) + 1 / 2) - a0 * Δ * ((Q.2 : ℝ) + 1 / 2) - b0| ≤ 49 * Δ := by
  set aT := tubeSlope T with haT_def
  set bT := tubeIntercept T with hbT_def
  set centerX := Δ * ((Q.1 : ℝ) + 1 / 2) with hcenterX_def
  set centerY := Δ * ((Q.2 : ℝ) + 1 / 2) with hcenterY_def
  have hδ_nonneg : 0 ≤ δ := by
    rw [hδ_eq] <;> positivity

  have h_res_T : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt (1 + aT ^ 2) * (2 * δ) :=
    residual_from_cthickening_local p_orig T (2 * δ) (by positivity) hT_dirV hp_on_T
  have h_res_T2 : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt 2 * (2 * δ) := by
    have h1 : Real.sqrt (1 + aT ^ 2) ≤ Real.sqrt 2 := by
      have h2 : 1 + aT ^ 2 ≤ 2 := by nlinarith [abs_le.mp hT_slope_bound]
      exact Real.sqrt_le_sqrt h2
    calc |p_orig 0 - aT * p_orig 1 - bT|
      ≤ Real.sqrt (1 + aT ^ 2) * (2 * δ) := h_res_T
    _ ≤ Real.sqrt 2 * (2 * δ) := by gcongr

  have h_dist_line : dist T T0 ≤ Δ := by simpa [InCoarseTube] using hT_in_T0
  have ha0_bound' : |(LemmaE.affineLineParams T0).1| ≤ 1 := by
    have h : (LemmaE.affineLineParams T0).1 = a0 := by
      simp [ha0_eq] <;> rfl
    rw [h]; exact ha0_bound
  have hb0_bound' : |(LemmaE.affineLineParams T0).2| ≤ 3 := by
    have h : (LemmaE.affineLineParams T0).2 = b0 := by
      simp [hb0_eq] <;> rfl
    rw [h]; exact hb0_bound
  have h_transfer : dist (tubeSlope T, tubeIntercept T) (tubeSlope T0, tubeIntercept T0) ≤
      8 * dist T T0 :=
    A9Support.bounded_metric_transfer T T0 hT_dirV hT0_dirV
      hT_slope_bound ha0_bound' hT_intercept_bound hb0_bound'
  have h_dist_params : dist (aT, bT) (a0, b0) ≤ 8 * Δ := by
    simpa [ha0_eq, hb0_eq] using h_transfer.trans (by linarith)
  have h_dist_def : dist (aT, bT) (a0, b0) = max (|aT - a0|) (|bT - b0|) := by
    simp [Prod.dist_eq] <;> rfl
  have h_da : |aT - a0| ≤ 8 * Δ := by
    rw [h_dist_def] at h_dist_params
    have h : |aT - a0| ≤ max (|aT - a0|) (|bT - b0|) := le_max_left _ _
    exact h.trans h_dist_params
  have h_db : |bT - b0| ≤ 8 * Δ := by
    rw [h_dist_def] at h_dist_params
    have h : |bT - b0| ≤ max (|aT - a0|) (|bT - b0|) := le_max_right _ _
    exact h.trans h_dist_params

  have h_infDist : Metric.infDist p_orig (squareSet Δ Q) ≤ 2 * Δ := by
    have h : Metric.infEDist p_orig (squareSet Δ Q) ≤ ENNReal.ofReal (2 * Δ) :=
      Metric.mem_cthickening_iff.mp hp_near_square
    have h2 : Metric.infDist p_orig (squareSet Δ Q) =
        ENNReal.toReal (Metric.infEDist p_orig (squareSet Δ Q)) := by rfl
    rw [h2]
    have h_top : ENNReal.ofReal (2 * Δ) ≠ ⊤ :=
      (ENNReal.ofReal_lt_top (r := 2 * Δ)).ne
    have h3 := ENNReal.toReal_mono h_top h
    rw [ENNReal.toReal_ofReal (by positivity)] at h3
    exact h3
  have h_strict : Metric.infDist p_orig (squareSet Δ Q) < 2 * Δ + Δ / 2 := by
    linarith [hΔ_pos]
  let q0 : Plane := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then Δ * (Q.1 : ℝ) else Δ * (Q.2 : ℝ))
  have hq0_mem : q0 ∈ squareSet Δ Q := by
    simp [squareSet, q0, Fin.sum_univ_two] <;> constructor <;> norm_num <;> linarith
  have h_exists_q : ∃ (q : Plane), q ∈ squareSet Δ Q ∧ dist p_orig q < 2 * Δ + Δ / 2 := by
    by_contra h
    push Not at h
    have h_lb : ∀ q ∈ squareSet Δ Q, (2 * Δ + Δ / 2 : ℝ) ≤ dist p_orig q := h
    have h_lb' : (2 * Δ + Δ / 2 : ℝ) ∈ lowerBounds (dist p_orig '' (squareSet Δ Q)) := by
      intro y hy
      rcases hy with ⟨q, hq, rfl⟩
      exact h_lb q hq
    have h_glb : IsGLB (dist p_orig '' (squareSet Δ Q)) (Metric.infDist p_orig (squareSet Δ Q)) :=
      Metric.isGLB_infDist (show (squareSet Δ Q).Nonempty from ⟨q0, hq0_mem⟩)
    have h_cont : (2 * Δ + Δ / 2 : ℝ) ≤ Metric.infDist p_orig (squareSet Δ Q) := h_glb.2 h_lb'
    linarith [h_infDist]
  rcases h_exists_q with ⟨q, hq_mem, hdist⟩
  have hq_x : q 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) := hq_mem.1
  have hq_y : q 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := hq_mem.2
  have h_qcx : |q 0 - centerX| ≤ Δ / 2 := by
    rw [abs_le] <;> constructor <;> linarith [hq_x.1, hq_x.2]
  have h_qcy : |q 1 - centerY| ≤ Δ / 2 := by
    rw [abs_le] <;> constructor <;> linarith [hq_y.1, hq_y.2]
  have hdist' : dist p_orig q ≤ 5 * Δ / 2 := by linarith
  have h_pcx : |p_orig 0 - centerX| ≤ 3 * Δ := by
    calc |p_orig 0 - centerX|
      = |(p_orig 0 - q 0) + (q 0 - centerX)| := by ring_nf
    _ ≤ |p_orig 0 - q 0| + |q 0 - centerX| := by exact DiscretisedFurstenbergEstimate.real_abs_add (p_orig.ofLp 0 - q.ofLp 0) (q.ofLp 0 - centerX)
    _ ≤ dist p_orig q + |q 0 - centerX| := by
      have h4 : |(p_orig - q) 0| ≤ ‖p_orig - q‖ := by exact TubesAndSlopes.coord_abs_le_norm (p_orig - q) 0
      have h5 : (p_orig - q) 0 = p_orig 0 - q 0 := by simp
      rw [h5] at h4
      have h6 : ‖p_orig - q‖ = dist p_orig q := by rw [dist_eq_norm]
      rw [h6] at h4
      linarith
    _ ≤ 5 * Δ / 2 + Δ / 2 := by linarith [hdist', h_qcx]
    _ = 3 * Δ := by ring
  have h_pcy : |p_orig 1 - centerY| ≤ 3 * Δ := by
    calc |p_orig 1 - centerY|
      = |(p_orig 1 - q 1) + (q 1 - centerY)| := by ring_nf
    _ ≤ |p_orig 1 - q 1| + |q 1 - centerY| := by exact DiscretisedFurstenbergEstimate.real_abs_add (p_orig.ofLp 1 - q.ofLp 1) (q.ofLp 1 - centerY)
    _ ≤ dist p_orig q + |q 1 - centerY| := by
      have h4 : |(p_orig - q) 1| ≤ ‖p_orig - q‖ := by exact TubesAndSlopes.coord_abs_le_norm (p_orig - q) 1
      have h5 : (p_orig - q) 1 = p_orig 1 - q 1 := by simp
      rw [h5] at h4
      have h6 : ‖p_orig - q‖ = dist p_orig q := by rw [dist_eq_norm]
      rw [h6] at h4
      linarith
    _ ≤ 5 * Δ / 2 + Δ / 2 := by linarith [hdist', h_qcy]
    _ = 3 * Δ := by ring

  have h_yQ : squareY Δ Q = Δ * (Q.2 : ℝ) := by simp [squareY] <;> ring
  have h_centerY_bounds : centerY ∈ Set.Icc (-2 : ℝ) (2 + Δ) := by
    have h1 : -2 ≤ Δ * (Q.2 : ℝ) := by
      rw [←h_yQ] <;> exact hy_Q_bounds.1
    have h2 : Δ * (Q.2 : ℝ) ≤ 2 := by
      rw [←h_yQ] <;> exact hy_Q_bounds.2
    constructor <;> linarith [hcenterY_def]
  have h_p1_bound : |p_orig 1| ≤ 2 + 4 * Δ := by
    have h1 : p_orig 1 ≤ centerY + 3 * Δ := by linarith [abs_le.mp h_pcy]
    have h2 : p_orig 1 ≥ centerY - 3 * Δ := by linarith [abs_le.mp h_pcy]
    rw [abs_le] <;> constructor <;> linarith [h_centerY_bounds.1, h_centerY_bounds.2]
  have h_p1_le : |p_orig 1| ≤ 4 := by
    have h6 : 2 + 4 * Δ ≤ 4 := by linarith [hΔ_le_half]
    linarith [h_p1_bound]

  have hδ_le : δ ≤ Δ := by
    rw [hδ_eq]
    have h7 : Δ ^ 2 ≤ Δ := by nlinarith
    exact h7

  have h_main : |centerX - a0 * centerY - b0| ≤
      |centerX - p_orig 0|
      + |p_orig 0 - aT * p_orig 1 - bT|
      + |aT - a0| * |p_orig 1|
      + |a0| * |p_orig 1 - centerY|
      + |bT - b0| := by
    have h_eq : centerX - a0 * centerY - b0 =
        (centerX - p_orig 0)
        + (p_orig 0 - aT * p_orig 1 - bT)
        + (aT - a0) * p_orig 1
        + a0 * (p_orig 1 - centerY)
        + (bT - b0) := by ring
    have h_abs1 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT)| ≤
        |centerX - p_orig 0| + |p_orig 0 - aT * p_orig 1 - bT| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add (centerX - p_orig.ofLp 0)
        (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT)
    have h_abs2 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1| ≤
        |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT)| + |(aT - a0) * p_orig 1| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add
        (centerX - p_orig.ofLp 0 + (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT)) ((aT - a0) * p_orig.ofLp 1)
    have h_abs3 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY)| ≤
        |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1| + |a0 * (p_orig 1 - centerY)| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add
        (centerX - p_orig.ofLp 0 + (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT) + (aT - a0) * p_orig.ofLp 1)
        (a0 * (p_orig.ofLp 1 - centerY))
    have h_abs4 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY) + (bT - b0)| ≤
        |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY)| + |bT - b0| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add
        (centerX - p_orig.ofLp 0 + (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT) + (aT - a0) * p_orig.ofLp 1 +
          a0 * (p_orig.ofLp 1 - centerY))
        (bT - b0)
    have h_bound : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY) + (bT - b0)| ≤
        |centerX - p_orig 0| + |p_orig 0 - aT * p_orig 1 - bT| + |(aT - a0) * p_orig 1| + |a0 * (p_orig 1 - centerY)| + |bT - b0| := by
      linarith [h_abs1, h_abs2, h_abs3, h_abs4]
    have h_final : |centerX - a0 * centerY - b0| = |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY) + (bT - b0)| := by
      rw [h_eq]
    rw [h_final]
    have h_simp : |(aT - a0) * p_orig 1| = |aT - a0| * |p_orig 1| := by rw [abs_mul]
    have h_simp2 : |a0 * (p_orig 1 - centerY)| = |a0| * |p_orig 1 - centerY| := by rw [abs_mul]
    rw [h_simp, h_simp2] at h_bound
    exact h_bound
  have h_goal : |Δ * ((Q.1 : ℝ) + 1 / 2) - a0 * Δ * ((Q.2 : ℝ) + 1 / 2) - b0| =
      |centerX - a0 * centerY - b0| := by
    have hcx : centerX = Δ * ((Q.1 : ℝ) + 1 / 2) := by simp [hcenterX_def]
    have hcy : centerY = Δ * ((Q.2 : ℝ) + 1 / 2) := by simp [hcenterY_def]
    rw [hcx, hcy] <;> ring_nf <;> rfl
  rw [h_goal]
  have h1 : |centerX - p_orig 0| ≤ 3 * Δ := by
    have h11 : |centerX - p_orig 0| = |p_orig 0 - centerX| := by
      rw [show centerX - p_orig 0 = -(p_orig 0 - centerX) by ring, abs_neg]
    rw [h11]; exact h_pcx
  have h34 : |aT - a0| * |p_orig 1| ≤ 32 * Δ := by
    calc |aT - a0| * |p_orig 1|
      ≤ (8 * Δ) * 4 := by gcongr <;> linarith
    _ = 32 * Δ := by ring
  have h56 : |a0| * |p_orig 1 - centerY| ≤ 3 * Δ := by
    calc |a0| * |p_orig 1 - centerY|
      ≤ 1 * (3 * Δ) := by gcongr <;> linarith
    _ = 3 * Δ := by ring
  have h_sqrt_delta : Real.sqrt 2 * δ ≤ Real.sqrt 2 * Δ :=
    mul_le_mul_of_nonneg_left hδ_le (by positivity)
  have h_sqrt_le_3 : 2 * Real.sqrt 2 ≤ 3 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h_final_bound : |centerX - a0 * centerY - b0| ≤ 49 * Δ := by
    calc |centerX - a0 * centerY - b0|
      ≤ |centerX - p_orig 0| + |p_orig 0 - aT * p_orig 1 - bT| + |aT - a0| * |p_orig 1| + |a0| * |p_orig 1 - centerY| + |bT - b0| := h_main
    _ ≤ 3 * Δ + Real.sqrt 2 * (2 * δ) + 32 * Δ + 3 * Δ + 8 * Δ := by
        have h2 : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt 2 * (2 * δ) := h_res_T2
        have h7 : |bT - b0| ≤ 8 * Δ := h_db
        linarith [h1, h2, h34, h56, h7]
    _ = 46 * Δ + 2 * Real.sqrt 2 * δ := by ring
    _ ≤ 46 * Δ + 2 * Real.sqrt 2 * Δ := by linarith [h_sqrt_delta]
    _ ≤ 49 * Δ := by
      have h12 : 2 * Real.sqrt 2 * Δ ≤ 3 * Δ := by
        gcongr <;> exact h_sqrt_le_3
      linarith
  exact h_final_bound

/-- Helper: same floor implies parameter difference < Δ. -/
lemma abs_sub_lt_of_same_floor {x y Δ : ℝ} (hΔ_pos : 0 < Δ)
    (h : ⌊x / Δ⌋ = ⌊y / Δ⌋) : |x - y| < Δ := by
  have h1 : (⌊x / Δ⌋ : ℝ) ≤ x / Δ := Int.floor_le _
  have h2 : x / Δ < (⌊x / Δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : (⌊y / Δ⌋ : ℝ) ≤ y / Δ := Int.floor_le _
  have h4 : y / Δ < (⌊y / Δ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  rw [h] at h1 h2
  have h5 : x / Δ - y / Δ < 1 := by linarith
  have h6 : y / Δ - x / Δ < 1 := by linarith
  have h7 : |x / Δ - y / Δ| < 1 := by
    rw [abs_lt] <;> constructor <;> linarith
  have h8 : |x - y| = Δ * |x / Δ - y / Δ| := by
    have h9 : x - y = Δ * (x / Δ - y / Δ) := by
      field_simp [hΔ_pos.ne'] <;> ring
    calc |x - y|
      = |Δ * (x / Δ - y / Δ)| := by rw [h9]
    _ = |Δ| * |x / Δ - y / Δ| := by exact abs_mul Δ (x / Δ - y / Δ)
    _ = Δ * |x / Δ - y / Δ| := by rw [abs_of_pos hΔ_pos]
  rw [h8]
  have h10 : Δ * |x / Δ - y / Δ| < Δ := by
    have h11 : Δ * |x / Δ - y / Δ| < Δ * 1 := by gcongr
    simpa using h11
  exact h10

/-- Core version of center_near_T0 taking parameter difference bounds directly. -/
lemma center_near_T0_core
    (Δ δ : ℝ) (hΔ_pos : 0 < Δ) (hδ_eq : δ = Δ ^ 2) (hΔ_le_half : Δ ≤ 1 / 2)
    (T0 T : FineTube)
    (a0 b0 : ℝ) (ha0_eq : a0 = tubeSlope T0) (hb0_eq : b0 = tubeIntercept T0)
    (ha0_bound : |a0| ≤ 1) (hb0_bound : |b0| ≤ 3)
    (hT_dirV : (LemmaE.getDirV T) 1 ≠ 0)
    (hT_slope_bound : |tubeSlope T| ≤ 1)
    (hT_intercept_bound : |tubeIntercept T| ≤ 3)
    (Q : CoarseSquare Δ)
    (p_orig : Plane)
    (hp_near_square : p_orig ∈ Metric.cthickening (2 * Δ) (squareSet Δ Q))
    (hp_on_T : p_orig ∈ Metric.cthickening (2 * δ) (T.1 : Set Plane))
    (h_da : |tubeSlope T - a0| ≤ 8 * Δ)
    (h_db : |tubeIntercept T - b0| ≤ 8 * Δ)
    (hy_Q_bounds : squareY Δ Q ∈ Set.Icc (-2 : ℝ) 2) :
    |Δ * ((Q.1 : ℝ) + 1 / 2) - a0 * Δ * ((Q.2 : ℝ) + 1 / 2) - b0| ≤ 49 * Δ := by
  set aT := tubeSlope T with haT_def
  set bT := tubeIntercept T with hbT_def
  set centerX := Δ * ((Q.1 : ℝ) + 1 / 2) with hcenterX_def
  set centerY := Δ * ((Q.2 : ℝ) + 1 / 2) with hcenterY_def
  have hδ_nonneg : 0 ≤ δ := by rw [hδ_eq] <;> positivity
  have h_res_T2 : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt 2 * (2 * δ) := by
    have h_res_T : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt (1 + aT ^ 2) * (2 * δ) :=
      residual_from_cthickening_local p_orig T (2 * δ) (by positivity) hT_dirV hp_on_T
    have h1 : Real.sqrt (1 + aT ^ 2) ≤ Real.sqrt 2 := by
      have h2 : 1 + aT ^ 2 ≤ 2 := by nlinarith [abs_le.mp hT_slope_bound]
      exact Real.sqrt_le_sqrt h2
    calc |p_orig 0 - aT * p_orig 1 - bT|
      ≤ Real.sqrt (1 + aT ^ 2) * (2 * δ) := h_res_T
    _ ≤ Real.sqrt 2 * (2 * δ) := by gcongr
  have h_infDist : Metric.infDist p_orig (squareSet Δ Q) ≤ 2 * Δ := by
    have h : Metric.infEDist p_orig (squareSet Δ Q) ≤ ENNReal.ofReal (2 * Δ) :=
      Metric.mem_cthickening_iff.mp hp_near_square
    have h2 : Metric.infDist p_orig (squareSet Δ Q) =
        ENNReal.toReal (Metric.infEDist p_orig (squareSet Δ Q)) := by rfl
    rw [h2]
    have h_top : ENNReal.ofReal (2 * Δ) ≠ ⊤ := (ENNReal.ofReal_lt_top (r := 2 * Δ)).ne
    have h3 := ENNReal.toReal_mono h_top h
    rw [ENNReal.toReal_ofReal (by positivity)] at h3
    exact h3
  have h_strict : Metric.infDist p_orig (squareSet Δ Q) < 2 * Δ + Δ / 2 := by linarith [hΔ_pos]
  let q0 : Plane := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then Δ * (Q.1 : ℝ) else Δ * (Q.2 : ℝ))
  have hq0_mem : q0 ∈ squareSet Δ Q := by
    simp [squareSet, q0, Fin.sum_univ_two] <;> constructor <;> norm_num <;> linarith
  have h_exists_q : ∃ (q : Plane), q ∈ squareSet Δ Q ∧ dist p_orig q < 2 * Δ + Δ / 2 := by
    by_contra h
    push Not at h
    have h_lb : ∀ q ∈ squareSet Δ Q, (2 * Δ + Δ / 2 : ℝ) ≤ dist p_orig q := h
    have h_lb' : (2 * Δ + Δ / 2 : ℝ) ∈ lowerBounds (dist p_orig '' (squareSet Δ Q)) := by
      intro y hy
      rcases hy with ⟨q, hq, rfl⟩
      exact h_lb q hq
    have h_glb : IsGLB (dist p_orig '' (squareSet Δ Q)) (Metric.infDist p_orig (squareSet Δ Q)) :=
      Metric.isGLB_infDist (show (squareSet Δ Q).Nonempty from ⟨q0, hq0_mem⟩)
    have h_cont : (2 * Δ + Δ / 2 : ℝ) ≤ Metric.infDist p_orig (squareSet Δ Q) := h_glb.2 h_lb'
    linarith [h_infDist]
  rcases h_exists_q with ⟨q, hq_mem, hdist⟩
  have hq_x : q 0 ∈ Set.Ico (Δ * (Q.1 : ℝ)) (Δ * ((Q.1 : ℝ) + 1)) := hq_mem.1
  have hq_y : q 1 ∈ Set.Ico (Δ * (Q.2 : ℝ)) (Δ * ((Q.2 : ℝ) + 1)) := hq_mem.2
  have h_qcx : |q 0 - centerX| ≤ Δ / 2 := by
    rw [abs_le] <;> constructor <;> linarith [hq_x.1, hq_x.2]
  have h_qcy : |q 1 - centerY| ≤ Δ / 2 := by
    rw [abs_le] <;> constructor <;> linarith [hq_y.1, hq_y.2]
  have hdist' : dist p_orig q ≤ 5 * Δ / 2 := by linarith
  have h_pcx : |p_orig 0 - centerX| ≤ 3 * Δ := by
    calc |p_orig 0 - centerX|
      = |(p_orig 0 - q 0) + (q 0 - centerX)| := by ring_nf
    _ ≤ |p_orig 0 - q 0| + |q 0 - centerX| := by exact DiscretisedFurstenbergEstimate.real_abs_add (p_orig.ofLp 0 - q.ofLp 0) (q.ofLp 0 - centerX)
    _ ≤ dist p_orig q + |q 0 - centerX| := by
      have h4 : |(p_orig - q) 0| ≤ ‖p_orig - q‖ := by exact TubesAndSlopes.coord_abs_le_norm (p_orig - q) 0
      have h5 : (p_orig - q) 0 = p_orig 0 - q 0 := by simp
      rw [h5] at h4
      have h6 : ‖p_orig - q‖ = dist p_orig q := by rw [dist_eq_norm]
      rw [h6] at h4
      linarith
    _ ≤ 5 * Δ / 2 + Δ / 2 := by linarith [hdist', h_qcx]
    _ = 3 * Δ := by ring
  have h_pcy : |p_orig 1 - centerY| ≤ 3 * Δ := by
    calc |p_orig 1 - centerY|
      = |(p_orig 1 - q 1) + (q 1 - centerY)| := by ring_nf
    _ ≤ |p_orig 1 - q 1| + |q 1 - centerY| := by exact DiscretisedFurstenbergEstimate.real_abs_add (p_orig.ofLp 1 - q.ofLp 1) (q.ofLp 1 - centerY)
    _ ≤ dist p_orig q + |q 1 - centerY| := by
      have h4 : |(p_orig - q) 1| ≤ ‖p_orig - q‖ := by exact TubesAndSlopes.coord_abs_le_norm (p_orig - q) 1
      have h5 : (p_orig - q) 1 = p_orig 1 - q 1 := by simp
      rw [h5] at h4
      have h6 : ‖p_orig - q‖ = dist p_orig q := by rw [dist_eq_norm]
      rw [h6] at h4
      linarith
    _ ≤ 5 * Δ / 2 + Δ / 2 := by linarith [hdist', h_qcy]
    _ = 3 * Δ := by ring
  have h_yQ : squareY Δ Q = Δ * (Q.2 : ℝ) := by simp [squareY] <;> ring
  have h_centerY_bounds : centerY ∈ Set.Icc (-2 : ℝ) (2 + Δ) := by
    have h1 : -2 ≤ Δ * (Q.2 : ℝ) := by rw [←h_yQ] <;> exact hy_Q_bounds.1
    have h2 : Δ * (Q.2 : ℝ) ≤ 2 := by rw [←h_yQ] <;> exact hy_Q_bounds.2
    constructor <;> linarith [hcenterY_def]
  have h_p1_bound : |p_orig 1| ≤ 2 + 4 * Δ := by
    have h1 : p_orig 1 ≤ centerY + 3 * Δ := by linarith [abs_le.mp h_pcy]
    have h2 : p_orig 1 ≥ centerY - 3 * Δ := by linarith [abs_le.mp h_pcy]
    rw [abs_le] <;> constructor <;> linarith [h_centerY_bounds.1, h_centerY_bounds.2]
  have h_p1_le : |p_orig 1| ≤ 4 := by
    have h6 : 2 + 4 * Δ ≤ 4 := by linarith [hΔ_le_half]
    linarith [h_p1_bound]
  have hδ_le : δ ≤ Δ := by
    rw [hδ_eq]
    have h7 : Δ ^ 2 ≤ Δ := by nlinarith
    exact h7
  have h_main : |centerX - a0 * centerY - b0| ≤
      |centerX - p_orig 0| + |p_orig 0 - aT * p_orig 1 - bT|
      + |aT - a0| * |p_orig 1| + |a0| * |p_orig 1 - centerY| + |bT - b0| := by
    have h_eq : centerX - a0 * centerY - b0 =
        (centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT)
        + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY) + (bT - b0) := by ring
    have h_abs1 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT)| ≤
        |centerX - p_orig 0| + |p_orig 0 - aT * p_orig 1 - bT| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add (centerX - p_orig.ofLp 0)
        (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT)
    have h_abs2 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1| ≤
        |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT)| + |(aT - a0) * p_orig 1| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add
        (centerX - p_orig.ofLp 0 + (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT)) ((aT - a0) * p_orig.ofLp 1)
    have h_abs3 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY)| ≤
        |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1| + |a0 * (p_orig 1 - centerY)| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add
        (centerX - p_orig.ofLp 0 + (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT) + (aT - a0) * p_orig.ofLp 1)
        (a0 * (p_orig.ofLp 1 - centerY))
    have h_abs4 : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY) + (bT - b0)| ≤
        |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY)| + |bT - b0| := by
      exact DiscretisedFurstenbergEstimate.real_abs_add
        (centerX - p_orig.ofLp 0 + (p_orig.ofLp 0 - aT * p_orig.ofLp 1 - bT) + (aT - a0) * p_orig.ofLp 1 +
          a0 * (p_orig.ofLp 1 - centerY))
        (bT - b0)
    have h_bound : |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY) + (bT - b0)| ≤
        |centerX - p_orig 0| + |p_orig 0 - aT * p_orig 1 - bT| + |(aT - a0) * p_orig 1| + |a0 * (p_orig 1 - centerY)| + |bT - b0| := by
      linarith [h_abs1, h_abs2, h_abs3, h_abs4]
    have h_final : |centerX - a0 * centerY - b0| = |(centerX - p_orig 0) + (p_orig 0 - aT * p_orig 1 - bT) + (aT - a0) * p_orig 1 + a0 * (p_orig 1 - centerY) + (bT - b0)| := by rw [h_eq]
    rw [h_final]
    have h_simp : |(aT - a0) * p_orig 1| = |aT - a0| * |p_orig 1| := by rw [abs_mul]
    have h_simp2 : |a0 * (p_orig 1 - centerY)| = |a0| * |p_orig 1 - centerY| := by rw [abs_mul]
    rw [h_simp, h_simp2] at h_bound
    exact h_bound
  have h_goal : |Δ * ((Q.1 : ℝ) + 1 / 2) - a0 * Δ * ((Q.2 : ℝ) + 1 / 2) - b0| =
      |centerX - a0 * centerY - b0| := by
    have hcx : centerX = Δ * ((Q.1 : ℝ) + 1 / 2) := by simp [hcenterX_def]
    have hcy : centerY = Δ * ((Q.2 : ℝ) + 1 / 2) := by simp [hcenterY_def]
    rw [hcx, hcy] <;> ring_nf <;> rfl
  rw [h_goal]
  have h1 : |centerX - p_orig 0| ≤ 3 * Δ := by
    have h11 : |centerX - p_orig 0| = |p_orig 0 - centerX| := by
      rw [show centerX - p_orig 0 = -(p_orig 0 - centerX) by ring, abs_neg]
    rw [h11]; exact h_pcx
  have h34 : |aT - a0| * |p_orig 1| ≤ 32 * Δ := by
    calc |aT - a0| * |p_orig 1|
      ≤ (8 * Δ) * 4 := by gcongr <;> linarith
    _ = 32 * Δ := by ring
  have h56 : |a0| * |p_orig 1 - centerY| ≤ 3 * Δ := by
    calc |a0| * |p_orig 1 - centerY|
      ≤ 1 * (3 * Δ) := by gcongr <;> linarith
    _ = 3 * Δ := by ring
  have h_sqrt_delta : Real.sqrt 2 * δ ≤ Real.sqrt 2 * Δ :=
    mul_le_mul_of_nonneg_left hδ_le (by positivity)
  have h_sqrt_le_3 : 2 * Real.sqrt 2 ≤ 3 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have h_final_bound : |centerX - a0 * centerY - b0| ≤ 49 * Δ := by
    calc |centerX - a0 * centerY - b0|
      ≤ |centerX - p_orig 0| + |p_orig 0 - aT * p_orig 1 - bT| + |aT - a0| * |p_orig 1| + |a0| * |p_orig 1 - centerY| + |bT - b0| := h_main
    _ ≤ 3 * Δ + Real.sqrt 2 * (2 * δ) + 32 * Δ + 3 * Δ + 8 * Δ := by
        have h2 : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt 2 * (2 * δ) := h_res_T2
        have h7 : |bT - b0| ≤ 8 * Δ := h_db
        linarith [h1, h2, h34, h56, h7]
    _ = 46 * Δ + 2 * Real.sqrt 2 * δ := by ring
    _ ≤ 46 * Δ + 2 * Real.sqrt 2 * Δ := by linarith [h_sqrt_delta]
    _ ≤ 49 * Δ := by
      have h12 : 2 * Real.sqrt 2 * Δ ≤ 3 * Δ := by
        gcongr <;> exact h_sqrt_le_3
      linarith
  exact h_final_bound

/-- Version of center_near_T0 using InParent (dyadic same-cell) instead of
    InCoarseTube (metric). -/
lemma center_near_T0_inParent
    (Δ δ : ℝ) (hΔ_pos : 0 < Δ) (hδ_eq : δ = Δ ^ 2) (hΔ_le_half : Δ ≤ 1 / 2)
    (T0 T : FineTube)
    (a0 b0 : ℝ) (ha0_eq : a0 = tubeSlope T0) (hb0_eq : b0 = tubeIntercept T0)
    (ha0_bound : |a0| ≤ 1) (hb0_bound : |b0| ≤ 3)
    (hT0_dirV : (LemmaE.getDirV T0) 1 ≠ 0)
    (hT_dirV : (LemmaE.getDirV T) 1 ≠ 0)
    (hT_slope_bound : |tubeSlope T| ≤ 1)
    (hT_intercept_bound : |tubeIntercept T| ≤ 3)
    (Q : CoarseSquare Δ)
    (p_orig : Plane)
    (hp_near_square : p_orig ∈ Metric.cthickening (2 * Δ) (squareSet Δ Q))
    (hp_on_T : p_orig ∈ Metric.cthickening (2 * δ) (T.1 : Set Plane))
    (h_in_parent : InParent Δ hΔ_pos T T0)
    (hy_Q_bounds : squareY Δ Q ∈ Set.Icc (-2 : ℝ) 2) :
    |Δ * ((Q.1 : ℝ) + 1 / 2) - a0 * Δ * ((Q.2 : ℝ) + 1 / 2) - b0| ≤ 49 * Δ := by
  set aT := tubeSlope T with haT_def
  set bT := tubeIntercept T with hbT_def
  have h_slope_floor : ⌊aT / Δ⌋ = ⌊a0 / Δ⌋ := by
    have h1 : parentCell Δ hΔ_pos T = parentCell Δ hΔ_pos T0 := h_in_parent
    simpa [parentCell, ha0_eq] using congr_arg Prod.fst h1
  have h_intercept_floor : ⌊bT / Δ⌋ = ⌊b0 / Δ⌋ := by
    have h1 : parentCell Δ hΔ_pos T = parentCell Δ hΔ_pos T0 := h_in_parent
    simpa [parentCell, hb0_eq] using congr_arg Prod.snd h1
  have h_da_lt : |aT - a0| < Δ := abs_sub_lt_of_same_floor hΔ_pos h_slope_floor
  have h_db_lt : |bT - b0| < Δ := abs_sub_lt_of_same_floor hΔ_pos h_intercept_floor
  have h_da : |aT - a0| ≤ 8 * Δ := by linarith
  have h_db : |bT - b0| ≤ 8 * Δ := by linarith
  exact center_near_T0_core Δ δ hΔ_pos hδ_eq hΔ_le_half T0 T a0 b0 ha0_eq hb0_eq
    ha0_bound hb0_bound hT_dirV hT_slope_bound hT_intercept_bound
    Q p_orig hp_near_square hp_on_T h_da h_db hy_Q_bounds

/-- Residual bound: if p_orig is within δ of a fine tube T which is within Δ of T0,
    then the horizontal residual from T0 is ≤ 50Δ. -/
lemma residual_T0_bound
    (Δ δ : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2) (hδ_eq : δ = Δ ^ 2)
    (T0 T : FineTube) (p_orig : Plane)
    (hT_dirV : (LemmaE.getDirV T) 1 ≠ 0)
    (hT0_dirV : (LemmaE.getDirV T0) 1 ≠ 0)
    (hT_slope_bound : |tubeSlope T| ≤ 1)
    (hT0_slope_bound : |tubeSlope T0| ≤ 1)
    (hT_intercept_bound : |tubeIntercept T| ≤ 3)
    (hT0_intercept_bound : |tubeIntercept T0| ≤ 3)
    (hp_on_T : p_orig ∈ Metric.cthickening (2 * δ) (T.1 : Set Plane))
    (hT_in_T0 : InCoarseTube Δ T T0)
    (hpy_abs : |p_orig 1| ≤ Real.sqrt 2) :
    |p_orig 0 - tubeSlope T0 * p_orig 1 - tubeIntercept T0| ≤ 50 * Δ := by
  set aT := tubeSlope T with haT
  set bT := tubeIntercept T with hbT
  set σ₀ := tubeSlope T0 with hσ0
  set h₀ := tubeIntercept T0 with hh0
  have hδ_nonneg : 0 ≤ δ := by rw [hδ_eq] <;> positivity
  have h_res_T : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt 2 * (2 * δ) := by
    have h1 := residual_from_cthickening_local p_orig T (2 * δ) (by positivity) hT_dirV hp_on_T
    have h2 : Real.sqrt (1 + aT ^ 2) ≤ Real.sqrt 2 := by
      have h3 : 1 + aT ^ 2 ≤ 2 := by nlinarith [abs_le.mp hT_slope_bound]
      exact Real.sqrt_le_sqrt h3
    calc |p_orig 0 - aT * p_orig 1 - bT|
      ≤ Real.sqrt (1 + aT ^ 2) * (2 * δ) := h1
    _ ≤ Real.sqrt 2 * (2 * δ) := by gcongr
  have h_transfer : dist (aT, bT) (σ₀, h₀) ≤ 8 * dist T T0 :=
    A9Support.bounded_metric_transfer T T0 hT_dirV hT0_dirV
      hT_slope_bound hT0_slope_bound hT_intercept_bound hT0_intercept_bound
  have h_dist_T : dist T T0 ≤ Δ := by simpa [InCoarseTube] using hT_in_T0
  have h_dist_params : dist (aT, bT) (σ₀, h₀) ≤ 8 * Δ := h_transfer.trans (by linarith)
  have h_da : |aT - σ₀| ≤ 8 * Δ := by
    have h : dist (aT, bT) (σ₀, h₀) = max (|aT - σ₀|) (|bT - h₀|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h] at h_dist_params
    exact le_trans (le_max_left _ _) h_dist_params
  have h_db : |bT - h₀| ≤ 8 * Δ := by
    have h : dist (aT, bT) (σ₀, h₀) = max (|aT - σ₀|) (|bT - h₀|) := by
      simp [Prod.dist_eq] <;> rfl
    rw [h] at h_dist_params
    exact le_trans (le_max_right _ _) h_dist_params
  have h_tri : |p_orig 0 - σ₀ * p_orig 1 - h₀| ≤
      |p_orig 0 - aT * p_orig 1 - bT| + |aT - σ₀| * |p_orig 1| + |bT - h₀| := by
    have h1 : p_orig 0 - σ₀ * p_orig 1 - h₀ =
        (p_orig 0 - aT * p_orig 1 - bT) + (aT - σ₀) * p_orig 1 + (bT - h₀) := by ring
    rw [h1]
    have h2 : |(p_orig 0 - aT * p_orig 1 - bT) + (aT - σ₀) * p_orig 1 + (bT - h₀)| ≤
        |p_orig 0 - aT * p_orig 1 - bT| + |(aT - σ₀) * p_orig 1| + |bT - h₀| := by
      set a := p_orig 0 - aT * p_orig 1 - bT with ha
      set b := (aT - σ₀) * p_orig 1 with hb
      set c := bT - h₀ with hc
      calc |a + b + c|
        = |a + (b + c)| := by ring_nf
      _ ≤ |a| + |b + c| := abs_add_le a (b + c)
      _ ≤ |a| + (|b| + |c|) := by gcongr; exact abs_add_le b c
      _ = |a| + |b| + |c| := by ring
    simpa [abs_mul] using h2
  have hδ_le_half : δ ≤ Δ := by
    rw [hδ_eq]
    have h1 : Δ < 1 := by linarith
    have h2 : Δ ^ 2 ≤ Δ := by
      calc Δ ^ 2 = Δ * Δ := by ring
        _ ≤ Δ * 1 := by gcongr <;> linarith
        _ = Δ := by ring
    exact h2
  have h_sqrt_le : Real.sqrt 2 ≤ 8 := by
    have h10 : Real.sqrt 2 ≤ Real.sqrt 64 := Real.sqrt_le_sqrt (by norm_num)
    have h11 : Real.sqrt 64 = 8 := by rw [Real.sqrt_eq_cases] <;> norm_num
    linarith
  calc |p_orig 0 - σ₀ * p_orig 1 - h₀|
    ≤ |p_orig 0 - aT * p_orig 1 - bT| + |aT - σ₀| * |p_orig 1| + |bT - h₀| := h_tri
  _ ≤ Real.sqrt 2 * (2 * δ) + 8 * Δ * Real.sqrt 2 + 8 * Δ := by
    have h1 : |p_orig 0 - aT * p_orig 1 - bT| ≤ Real.sqrt 2 * (2 * δ) := h_res_T
    have h2 : |aT - σ₀| * |p_orig 1| ≤ 8 * Δ * Real.sqrt 2 := by
      calc |aT - σ₀| * |p_orig 1|
        ≤ (8 * Δ) * |p_orig 1| := mul_le_mul_of_nonneg_right h_da (by positivity)
      _ ≤ (8 * Δ) * Real.sqrt 2 := by gcongr <;> linarith
      _ = 8 * Δ * Real.sqrt 2 := by ring
    have h3 : |bT - h₀| ≤ 8 * Δ := h_db
    linarith
  _ = 2 * Real.sqrt 2 * δ + 8 * Real.sqrt 2 * Δ + 8 * Δ := by ring
  _ ≤ 2 * Real.sqrt 2 * Δ + 8 * Real.sqrt 2 * Δ + 8 * Δ := by gcongr <;> linarith [hδ_le_half]
  _ = (10 * Real.sqrt 2 + 8) * Δ := by ring
  _ ≤ 50 * Δ := by
    have h4 : 10 * Real.sqrt 2 + 8 ≤ 50 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact mul_le_mul_of_nonneg_right h4 hΔ_pos.le

/-- Geometric row bound: if all square centers have horizontal deviation ≤ K*Δ
    from a line x = a*y + b, then each y-row has ≤ 100 squares (0 ≤ K ≤ 49). -/
lemma row_bound_from_horizontal_deviation
    (Δ : ℝ) (hΔ_pos : 0 < Δ)
    (a b : ℝ)
    (Q0 : Finset (CoarseSquare Δ))
    (K : ℝ) (hK_nonneg : 0 ≤ K) (hK_le : K ≤ 59)
    (h_dev : ∀ Q ∈ Q0,
      |Δ * ((Q.1 : ℝ) + 1 / 2) - a * Δ * ((Q.2 : ℝ) + 1 / 2) - b| ≤ K * Δ) :
    ∀ (y : ℝ), (Q0.filter (fun Q => squareY Δ Q = y)).card ≤ 120 := by
  intro y
  let R := Q0.filter (fun Q => squareY Δ Q = y)
  have h_row : ∀ Q ∈ R, squareY Δ Q = y := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  have h_sub : R ⊆ Q0 := Finset.filter_subset _ _
  have h_y_fixed : ∀ Q ∈ R, (Q.2 : ℝ) = y / Δ := by
    intro Q hQ
    have h_y : squareY Δ Q = y := h_row Q hQ
    have h1 : squareY Δ Q = Δ * (Q.2 : ℝ) := by simp [squareY] <;> ring
    rw [h1] at h_y
    field_simp [hΔ_pos.ne'] at h_y ⊢ <;> linarith
  let c : ℝ := a * (y / Δ + 1 / 2) + b / Δ - 1 / 2
  have h_interval : ∀ Q ∈ R, (Q.1 : ℝ) ∈ Set.Icc (c - K) (c + K) := by
    intro Q hQ
    have hQ0 : Q ∈ Q0 := h_sub hQ
    have h_devQ := h_dev Q hQ0
    have h_j : (Q.2 : ℝ) = y / Δ := h_y_fixed Q hQ
    have h9 : |Δ * ((Q.1 : ℝ) + 1 / 2) - a * Δ * ((Q.2 : ℝ) + 1 / 2) - b| ≤ K * Δ := h_devQ
    have h10 : |(Q.1 : ℝ) + 1 / 2 - (a * ((Q.2 : ℝ) + 1 / 2) + b / Δ)| ≤ K := by
      have h11 : Δ * ((Q.1 : ℝ) + 1 / 2) - a * Δ * ((Q.2 : ℝ) + 1 / 2) - b =
          Δ * ((Q.1 : ℝ) + 1 / 2 - (a * ((Q.2 : ℝ) + 1 / 2) + b / Δ)) := by
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h11] at h9
      have h12 : |Δ * ((Q.1 : ℝ) + 1 / 2 - (a * ((Q.2 : ℝ) + 1 / 2) + b / Δ))| =
          Δ * |(Q.1 : ℝ) + 1 / 2 - (a * ((Q.2 : ℝ) + 1 / 2) + b / Δ)| := by
        rw [abs_mul, abs_of_pos hΔ_pos] <;> ring
      rw [h12] at h9
      have h13 : (Δ * |(Q.1 : ℝ) + 1 / 2 - (a * ((Q.2 : ℝ) + 1 / 2) + b / Δ)|) / Δ ≤ (K * Δ) / Δ := by
        gcongr
      have h14 : (Δ * |(Q.1 : ℝ) + 1 / 2 - (a * ((Q.2 : ℝ) + 1 / 2) + b / Δ)|) / Δ =
          |(Q.1 : ℝ) + 1 / 2 - (a * ((Q.2 : ℝ) + 1 / 2) + b / Δ)| := by
        field_simp [hΔ_pos.ne'] <;> ring
      have h15 : (K * Δ) / Δ = K := by
        field_simp [hΔ_pos.ne'] <;> ring
      rw [h14, h15] at h13
      exact h13
    rw [h_j] at h10
    have h13 : |(Q.1 : ℝ) - c| ≤ K := by
      have h14 : (Q.1 : ℝ) - c = (Q.1 : ℝ) + 1 / 2 - (a * (y / Δ + 1 / 2) + b / Δ) := by
        simp [c] <;> ring
      rw [h14]
      exact h10
    have h15 : -K ≤ (Q.1 : ℝ) - c := (abs_le.mp h13).1
    have h16 : (Q.1 : ℝ) - c ≤ K := (abs_le.mp h13).2
    have h17 : c - K ≤ (Q.1 : ℝ) := by linarith
    have h18 : (Q.1 : ℝ) ≤ c + K := by linarith
    exact ⟨h17, h18⟩
  have h_inj : Set.InjOn (fun (Q : CoarseSquare Δ) => Q.1) (R : Set (CoarseSquare Δ)) := by
    intro Q1 hQ1 Q2 hQ2 h_eq
    have h_j1 : (Q1.2 : ℝ) = y / Δ := h_y_fixed Q1 hQ1
    have h_j2 : (Q2.2 : ℝ) = y / Δ := h_y_fixed Q2 hQ2
    have h_j_eq : Q1.2 = Q2.2 := by
      exact_mod_cast Eq.trans h_j1 h_j2.symm
    exact Prod.ext h_eq h_j_eq
  let lo : ℤ := ⌊c - K⌋
  let hi : ℤ := ⌈c + K⌉
  have h_lo_lt : (c - K : ℝ) - 1 < (lo : ℝ) := Int.sub_one_lt_floor (c - K)
  have h_hi_lt : (hi : ℝ) < (c + K : ℝ) + 1 := Int.ceil_lt_add_one (c + K)
  have h_lo_le_hi : lo ≤ hi := by
    have h1 : (lo : ℝ) ≤ c - K := Int.floor_le (c - K)
    have h2 : c - K ≤ c + K := by linarith [hK_nonneg]
    have h3 : c + K ≤ (hi : ℝ) := Int.le_ceil (c + K)
    have h4 : (lo : ℝ) ≤ (hi : ℝ) := by linarith
    exact_mod_cast h4
  have h_diff_lt : (hi : ℝ) - (lo : ℝ) < 2 * K + 2 := by linarith [hK_nonneg]
  have h_diff_le : hi - lo ≤ 119 := by
    have h4 : (hi : ℝ) - (lo : ℝ) < 120 := by
      have h5 : 2 * K + 2 ≤ 120 := by linarith [hK_le]
      linarith
    have h6 : hi - lo < 120 := by exact_mod_cast h4
    exact Int.lt_add_one_iff.mp h6
  have h_sub2 : (R.image (fun Q : CoarseSquare Δ => Q.1)) ⊆ Finset.Icc lo hi := by
    intro i hi'
    rcases Finset.mem_image.mp hi' with ⟨Q, hQ, rfl⟩
    have h13 : (Q.1 : ℝ) ∈ Set.Icc (c - K) (c + K) := h_interval Q hQ
    simp only [Finset.mem_Icc, lo, hi]
    constructor
    · have h14 : (lo : ℝ) ≤ c - K := Int.floor_le (c - K)
      have h15 : c - K ≤ (Q.1 : ℝ) := h13.1
      exact_mod_cast le_trans h14 h15
    · have h16 : (Q.1 : ℝ) ≤ c + K := h13.2
      have h17 : c + K ≤ (hi : ℝ) := Int.le_ceil (c + K)
      exact_mod_cast le_trans h16 h17
  have h7 : 0 ≤ hi - lo := by linarith [h_lo_le_hi]
  have h11 : 0 ≤ hi - lo + 1 := by linarith
  have h_card : (Finset.Icc lo hi).card ≤ 120 := by
    have h_card_eq : (Finset.Icc lo hi).card = (hi - lo + 1).toNat := by
      have h : (Finset.Icc lo hi).card = (1 + hi - lo).toNat := by
        rw [Int.card_Icc]
        <;> congr 1 <;> omega
      rw [h] <;> congr <;> ring
    rw [h_card_eq]
    have h10 : hi - lo + 1 ≤ 120 := by linarith [h_diff_le]
    have h13 : ((hi - lo + 1).toNat : ℤ) = hi - lo + 1 := Int.toNat_of_nonneg h11
    have h14 : ((hi - lo + 1).toNat : ℤ) ≤ 120 := by
      rw [h13] <;> linarith
    exact_mod_cast h14
  have h22 : (R.image (fun Q : CoarseSquare Δ => Q.1)).card ≤ (Finset.Icc lo hi).card :=
    Finset.card_le_card h_sub2
  have h_image_card : (R.image (fun Q : CoarseSquare Δ => Q.1)).card = R.card :=
    Finset.card_image_of_injOn h_inj
  have h_final : R.card ≤ 120 := by
    rw [←h_image_card]
    exact h22.trans h_card
  exact h_final

/-- Modified hY_bounded_fiber: takes near-condition hypothesis and
    applies the row bound. The caller must prove h_near from A8 data. -/
lemma A9_hY_bounded_fiber_with_near
    (Δ δ s t ε : ℝ) (hΔ_pos : 0 < Δ)
    (Q0 : Finset (CoarseSquare Δ))
    (perSquare : ∀ (Q : CoarseSquare Δ), Q ∈ Q0 → A9_SquareData Δ δ s t ε Q)
    (a b : ℝ)
    (K : ℝ) (hK_nonneg : 0 ≤ K) (hK_le : K ≤ 59)
    (h_near : ∀ Q ∈ Q0,
      |Δ * ((Q.1 : ℝ) + 1 / 2) - a * Δ * ((Q.2 : ℝ) + 1 / 2) - b| ≤ K * Δ) :
    ∀ y : ℝ, (Q0.attach.filter (fun Q' =>
      (perSquare Q'.val Q'.property).y_Q = y)).card ≤ 120 := by
  have h_yQ_eq : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q0),
      (perSquare Q hQ).y_Q = squareY Δ Q := by
    intro Q hQ
    exact (perSquare Q hQ).hy_Q_eq
  intro y
  let R_attach := Q0.attach.filter (fun Q' => (perSquare Q'.val Q'.property).y_Q = y)
  let R_plain := Q0.filter (fun Q => squareY Δ Q = y)
  let f : {x // x ∈ Q0} → CoarseSquare Δ := fun Q => Q.val
  have h_inj : Set.InjOn f (R_attach : Set {x // x ∈ Q0}) := by
    intro Q1 _ Q2 _ h
    exact Subtype.ext h
  have h_image : R_attach.image f = R_plain := by
    ext Q
    simp only [R_attach, R_plain, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨Q', hQ', rfl⟩
      have h1 : (perSquare Q'.val Q'.property).y_Q = y := hQ'.2
      have h2 : squareY Δ Q'.val = (perSquare Q'.val Q'.property).y_Q :=
        (h_yQ_eq Q'.val Q'.property).symm
      exact ⟨Q'.property, by rw [h2, h1]⟩
    · intro hQ
      refine ⟨⟨Q, hQ.1⟩, ?_, rfl⟩
      have h1 : squareY Δ Q = y := hQ.2
      have h2 : (perSquare Q hQ.1).y_Q = squareY Δ Q := h_yQ_eq Q hQ.1
      exact ⟨show (⟨Q, hQ.1⟩ : {x // x ∈ Q0}) ∈ Q0.attach from by simp, by rw [h2, h1]⟩
  have h_eq_cards : R_attach.card = R_plain.card := by
    have h : (R_attach.image f).card = R_attach.card := Finset.card_image_of_injOn h_inj
    rw [←h, h_image]
  rw [h_eq_cards]
  exact row_bound_from_horizontal_deviation Δ hΔ_pos a b Q0 K hK_nonneg hK_le h_near y

-- Standalone lemma: total fine cell cardinality bounded by sum of assignedCounts.
lemma A9_total_fine_cells_bound
    (Δ δ s t ε : ℝ)
    (Q0 : Finset (CoarseSquare Δ))
    (perSquare' : ∀ (Q : CoarseSquare Δ), Q ∈ Q0 → A9_SquareData Δ δ s t ε Q) :
    (Q0.attach.biUnion (fun Q' =>
      (perSquare' Q'.val Q'.property).P_norm_Q.biUnion (fun p =>
        (perSquare' Q'.val Q'.property).fineTubes_norm p))).card ≤
    ∑ Q' ∈ Q0.attach,
      ∑ p ∈ (perSquare' Q'.val Q'.property).P_phys,
        assignedCountDyadic Δ (perSquare' Q'.val Q'.property).hΔ_pos
          (perSquare' Q'.val Q'.property).T_Q p
          (perSquare' Q'.val Q'.property).T0 := by
  let outerFun (Q' : {Q // Q ∈ Q0}) : Finset (DyadicTubeCell δ) :=
    (perSquare' Q'.val Q'.property).P_norm_Q.biUnion (fun p =>
      (perSquare' Q'.val Q'.property).fineTubes_norm p)
  have h1a : (Q0.attach.biUnion outerFun).card ≤ ∑ Q' ∈ Q0.attach, (outerFun Q').card :=
    Finset.card_biUnion_le
  have h1b : ∑ Q' ∈ Q0.attach, (outerFun Q').card ≤
      ∑ Q' ∈ Q0.attach, ∑ p ∈ (perSquare' Q'.val Q'.property).P_norm_Q,
        ((perSquare' Q'.val Q'.property).fineTubes_norm p).card := by
    apply Finset.sum_le_sum
    intro Q' _
    exact Finset.card_biUnion_le
  have h1 : (Q0.attach.biUnion outerFun).card ≤
      ∑ Q' ∈ Q0.attach, ∑ p ∈ (perSquare' Q'.val Q'.property).P_norm_Q,
        ((perSquare' Q'.val Q'.property).fineTubes_norm p).card :=
    le_trans h1a h1b
  have h2 : ∀ Q' ∈ Q0.attach,
      ∑ p ∈ (perSquare' Q'.val Q'.property).P_norm_Q,
        ((perSquare' Q'.val Q'.property).fineTubes_norm p).card ≤
      ∑ p ∈ (perSquare' Q'.val Q'.property).P_phys,
        assignedCountDyadic Δ (perSquare' Q'.val Q'.property).hΔ_pos
          (perSquare' Q'.val Q'.property).T_Q p
          (perSquare' Q'.val Q'.property).T0 := by
    intro Q' _
    exact (perSquare' Q'.val Q'.property).hfine_sum_le
  have h3 : ∑ Q' ∈ Q0.attach,
        ∑ p ∈ (perSquare' Q'.val Q'.property).P_norm_Q,
          ((perSquare' Q'.val Q'.property).fineTubes_norm p).card ≤
      ∑ Q' ∈ Q0.attach,
        ∑ p ∈ (perSquare' Q'.val Q'.property).P_phys,
          assignedCountDyadic Δ (perSquare' Q'.val Q'.property).hΔ_pos
            (perSquare' Q'.val Q'.property).T_Q p
            (perSquare' Q'.val Q'.property).T0 := by
    apply Finset.sum_le_sum
    intro Q' hQ'
    exact h2 Q' hQ'
  exact le_trans h1 h3

/-- Snapping a point to the δ-grid: each coordinate is rounded down to the nearest
    multiple of δ. The distance from the original point to the snapped point is at most δ. -/
lemma snap_to_grid_dist_le (δ : ℝ) (hδ_pos : 0 < δ) (x : ℝ × ℝ) :
    dist x (δ * ⌊x.1 / δ⌋, δ * ⌊x.2 / δ⌋) ≤ δ := by
  have h1 : 0 ≤ x.1 - δ * ⌊x.1 / δ⌋ := by
    have h : (⌊x.1 / δ⌋ : ℝ) ≤ x.1 / δ := Int.floor_le (x.1 / δ)
    have h2 : δ * (⌊x.1 / δ⌋ : ℝ) ≤ x.1 := by
      calc δ * (⌊x.1 / δ⌋ : ℝ) ≤ δ * (x.1 / δ) := by gcongr
        _ = x.1 := by field_simp [hδ_pos.ne'] <;> ring
    linarith
  have h2 : x.1 - δ * ⌊x.1 / δ⌋ < δ := by
    have h : x.1 / δ < (⌊x.1 / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (x.1 / δ)
    have h3 : x.1 < δ * ((⌊x.1 / δ⌋ : ℝ) + 1) := by
      calc x.1 = δ * (x.1 / δ) := by field_simp [hδ_pos.ne'] <;> ring
        _ < δ * ((⌊x.1 / δ⌋ : ℝ) + 1) := by gcongr
    linarith
  have h4 : 0 ≤ x.2 - δ * ⌊x.2 / δ⌋ := by
    have h : (⌊x.2 / δ⌋ : ℝ) ≤ x.2 / δ := Int.floor_le (x.2 / δ)
    have h2 : δ * (⌊x.2 / δ⌋ : ℝ) ≤ x.2 := by
      calc δ * (⌊x.2 / δ⌋ : ℝ) ≤ δ * (x.2 / δ) := by gcongr
        _ = x.2 := by field_simp [hδ_pos.ne'] <;> ring
    linarith
  have h5 : x.2 - δ * ⌊x.2 / δ⌋ < δ := by
    have h : x.2 / δ < (⌊x.2 / δ⌋ : ℝ) + 1 := Int.lt_floor_add_one (x.2 / δ)
    have h3 : x.2 < δ * ((⌊x.2 / δ⌋ : ℝ) + 1) := by
      calc x.2 = δ * (x.2 / δ) := by field_simp [hδ_pos.ne'] <;> ring
        _ < δ * ((⌊x.2 / δ⌋ : ℝ) + 1) := by gcongr
    linarith
  have h6 : |x.1 - δ * ⌊x.1 / δ⌋| < δ := by
    rw [abs_of_nonneg h1] <;> linarith
  have h7 : |x.2 - δ * ⌊x.2 / δ⌋| < δ := by
    rw [abs_of_nonneg h4] <;> linarith
  have h_lt : dist x (δ * ⌊x.1 / δ⌋, δ * ⌊x.2 / δ⌋) < δ := by
    simpa [Prod.dist_eq, max_lt_iff] using ⟨h6, h7⟩
  exact le_of_lt h_lt

/-- Core residual bound for A9: given an original tube close to p_orig and a
    dyadically-quantized reconstructed tube, the residual of the reconstructed
    tube at the sheared x-coordinate is at most 6δ.

    This extracts the algebraic core of `h_residual` from A9_PerSquareBuild. -/
lemma residual_bound_core
    (δ : ℝ) (hδ_pos : 0 < δ)
    (σ₀ h₀ : ℝ)
    (p_orig : Plane)
    (a_orig b_orig : ℝ)
    (ha_bound : |a_orig| ≤ 1)
    (h_py_abs : |p_orig 1| ≤ Real.sqrt 2)
    (h_res_orig : |p_orig 0 - a_orig * p_orig 1 - b_orig| ≤ Real.sqrt (1 + a_orig^2) * (2 * δ))
    (a_T b_T : ℝ)
    (ha_quant1 : 0 ≤ (a_orig - σ₀) - a_T)
    (ha_quant2 : (a_orig - σ₀) - a_T < δ)
    (hb_quant1 : 0 ≤ (b_orig - h₀) - b_T)
    (hb_quant2 : (b_orig - h₀) - b_T < δ)
    (x' : ℝ)
    (hx'_eq : x' = p_orig 0 - σ₀ * p_orig 1 - h₀) :
    |x' - a_T * p_orig 1 - b_T| ≤ 6 * δ := by
  set a' : ℝ := a_orig - σ₀ with ha'_def
  set b' : ℝ := b_orig - h₀ with hb'_def
  set A : ℝ := p_orig 0 - a_orig * p_orig 1 - b_orig with hA_def
  set B : ℝ := (a' - a_T) * p_orig 1 with hB_def
  set C : ℝ := b' - b_T with hC_def
  have h4 : |A + B + C| ≤ |A| + |B| + |C| := by
    calc |A + B + C| ≤ |A + B| + |C| := by exact DiscretisedFurstenbergEstimate.real_abs_add (A + B) C
      _ ≤ (|A| + |B|) + |C| := by gcongr <;> exact DiscretisedFurstenbergEstimate.real_abs_add A B
      _ = |A| + |B| + |C| := by ring
  have h7 : |B| = |a' - a_T| * |p_orig 1| := by
    simp [hB_def, abs_mul]
  have h_sq : a_orig^2 ≤ 1 := by
    have h52 : |a_orig| ≤ 1 := ha_bound
    have h53 : a_orig^2 = |a_orig|^2 := by rw [sq_abs]
    rw [h53]
    have h54 : |a_orig|^2 ≤ 1 := by
      have h55 : |a_orig| ≤ 1 := h52
      have h56 : |a_orig|^2 ≤ 1 := by
        calc |a_orig|^2 ≤ 1^2 := by gcongr
          _ = 1 := by norm_num
      exact h56
    exact h54
  have h_sqrt2 : Real.sqrt (1 + a_orig^2) ≤ Real.sqrt 2 := by
    have h_goal : 1 + a_orig^2 ≤ 2 := by
      have h : a_orig^2 ≤ 1 := h_sq
      linarith
    exact Real.sqrt_le_sqrt h_goal
  have h_abs_a : |a' - a_T| = a' - a_T := by
    rw [abs_of_nonneg ha_quant1]
  have h_abs_C : |C| = b' - b_T := by
    have h12 : 0 ≤ b' - b_T := hb_quant1
    rw [abs_of_nonneg h12] <;> simp [hC_def]
  have h11 : Real.sqrt 2 * (2 * δ) < 3 * δ := by
    have h12 : Real.sqrt 2 < 3 / 2 := by
      have h13 : Real.sqrt 2 < Real.sqrt (9 / 4) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h14 : Real.sqrt (9 / 4) = 3 / 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h14] at h13
      exact h13
    have h15 : 0 < δ := hδ_pos
    nlinarith
  have h14 : |A| < 3 * δ := by
    calc |A|
      ≤ Real.sqrt (1 + a_orig^2) * (2 * δ) := h_res_orig
    _ ≤ Real.sqrt 2 * (2 * δ) := by gcongr
    _ < 3 * δ := h11
  have h18 : |a' - a_T| * |p_orig 1| ≤ Real.sqrt 2 * δ := by
    rw [h_abs_a]
    have h19 : |p_orig 1| ≤ Real.sqrt 2 := h_py_abs
    calc (a' - a_T) * |p_orig 1| ≤ (a' - a_T) * Real.sqrt 2 := by gcongr
      _ = Real.sqrt 2 * (a' - a_T) := by ring
      _ ≤ Real.sqrt 2 * δ := by gcongr <;> exact le_of_lt ha_quant2
  have h20 : |C| ≤ δ := by
    rw [h_abs_C]
    exact le_of_lt hb_quant2
  have h_final_lt : |A| + |a' - a_T| * |p_orig 1| + |C| < 6 * δ := by
    calc |A| + |a' - a_T| * |p_orig 1| + |C|
      < 3 * δ + (|a' - a_T| * |p_orig 1|) + |C| := by gcongr
    _ ≤ 3 * δ + Real.sqrt 2 * δ + δ := by gcongr
    _ = (4 + Real.sqrt 2) * δ := by ring
    _ ≤ 6 * δ := by
      have h_sqrt2_le : Real.sqrt 2 ≤ 2 := by
        have h3 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        have h4 : Real.sqrt 4 = 2 := by
          rw [Real.sqrt_eq_cases] <;> norm_num
        rw [h4] at h3
        exact h3
      have h : 4 + Real.sqrt 2 ≤ 6 := by linarith
      gcongr <;> linarith
  have h4' : |A + B + C| ≤ |A| + |a' - a_T| * |p_orig 1| + |C| := by
    rw [h7] at h4
    exact h4
  have h_alg : x' - a_T * p_orig 1 - b_T = A + B + C := by
    have h3 : x' = p_orig 0 - σ₀ * p_orig 1 - h₀ := hx'_eq
    rw [h3]
    simp [hA_def, hB_def, hC_def, ha'_def, hb'_def] <;> ring
  rw [h_alg]
  exact le_trans h4' (le_of_lt h_final_lt)

/-- Extract coarse parameter S-set bound from A4 square data.

    Given A4's C_Q_pi with its S-set and tube parameter bounds, proves that
    the image under (slope, intercept) is a (Δ, s, Δ^{-60ε})-set. -/
lemma coarseParams_sset_bound
    (Δ δ s t ε : ℝ) (Q : CoarseSquare Δ) (hΔ_pos : 0 < Δ)
    (hs_nonneg : 0 ≤ s) (hs1 : s < 1) (hε_pos : 0 < ε)
    (hΔ_coarse_absorb : (2 * 10^13 : ℝ) ≤ Real.rpow Δ (-ε))
    (a4 : A4_SquareData Δ δ s t ε Q) :
    IsDeltaSSet Δ s (Real.rpow Δ (-60 * ε))
      ((fun T : CoarseTube => (tubeSlope T, tubeIntercept T)) '' (a4.C_Q_pi : Set CoarseTube)) := by
  let base := a4.base
  let C_Q_pi := a4.C_Q_pi
  let P : Set CoarseTube := (C_Q_pi : Set CoarseTube)
  have hC_Q_pi_sset : IsDeltaSSet Δ s (Real.rpow Δ (-59 * ε)) P :=
    a4.hC_Q_pi_sset
  have h_slope : ∀ T ∈ P, |tubeSlope T| ≤ 1 := by
    intro T hT
    have hT' : T ∈ base.C_Q := a4.hC_Q_pi_sub hT
    exact base.hC_Q_slope_bound T hT'
  have h_dir : ∀ T ∈ P, (LemmaE.getDirV T) 1 ≠ 0 := by
    intro T hT
    have hT' : T ∈ base.C_Q := a4.hC_Q_pi_sub hT
    exact base.hC_Q_v T hT'
  have h_intercept : ∀ T ∈ P, |tubeIntercept T| ≤ (3 : ℝ) := by
    intro T hT
    have hT' : T ∈ base.C_Q := a4.hC_Q_pi_sub hT
    exact base.hC_Q_b T hT'
  have h_transfer := coarseParams_sset_transfer
    (hΔ_pos := hΔ_pos) (hs_nonneg := hs_nonneg) (hB_nonneg := by norm_num)
    (hP := hC_Q_pi_sset) (h_dir := h_dir) (h_slope := h_slope) (h_intercept := h_intercept)
  have h_const_le : (200000 : ℝ) * (2 + 2 * (3 : ℝ)) ^ 4 * (3 + (3 : ℝ)) ^ 4 *
      (2 * (3 + (3 : ℝ))) ^ s * Real.rpow Δ (-59 * ε) ≤
      Real.rpow Δ (-60 * ε) := by
    have h1 : (200000 : ℝ) * (2 + 2 * (3 : ℝ)) ^ 4 * (3 + (3 : ℝ)) ^ 4 *
        (2 * (3 + (3 : ℝ))) ^ s ≤ (2 * 10^13 : ℝ) := by
      have hs_nonneg' : 0 ≤ s := hs_nonneg
      have h2 : (2 * (3 + (3 : ℝ))) ^ s ≤ (12 : ℝ) := by
        have h_base : 1 ≤ (2 * (3 + (3 : ℝ))) := by norm_num
        have h_s_le_one : s ≤ (1 : ℝ) := by linarith [hs1]
        have h_rpow : (2 * (3 + (3 : ℝ))) ^ s ≤ (2 * (3 + (3 : ℝ))) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h_base h_s_le_one
        have h_one : (2 * (3 + (3 : ℝ))) ^ (1 : ℝ) = (12 : ℝ) := by
          rw [Real.rpow_one] <;> norm_num
        rw [h_one] at h_rpow
        exact h_rpow
      have h_nonneg1 : 0 ≤ (200000 : ℝ) * (2 + 2 * (3 : ℝ)) ^ 4 * (3 + (3 : ℝ)) ^ 4 := by positivity
      have h : (200000 : ℝ) * (2 + 2 * (3 : ℝ)) ^ 4 * (3 + (3 : ℝ)) ^ 4 *
          (2 * (3 + (3 : ℝ))) ^ s ≤
          (200000 : ℝ) * (2 + 2 * (3 : ℝ)) ^ 4 * (3 + (3 : ℝ)) ^ 4 * (12 : ℝ) := by
        gcongr <;> linarith
      have h_final : (200000 : ℝ) * (2 + 2 * (3 : ℝ)) ^ 4 * (3 + (3 : ℝ)) ^ 4 * (12 : ℝ) ≤
          (2 * 10^13 : ℝ) := by norm_num
      linarith
    have h4 : Real.rpow Δ (-60 * ε) = Real.rpow Δ (-ε) * Real.rpow Δ (-59 * ε) := by
      have h5 : (-60 * ε) = (-ε) + (-59 * ε) := by ring
      rw [h5]
      exact Real.rpow_add hΔ_pos (-ε) (-59 * ε)
    rw [h4]
    have h5 : (0 : ℝ) < Real.rpow Δ (-59 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    gcongr
    have h6 : (200000 : ℝ) * (2 + 2 * (3 : ℝ)) ^ 4 * (3 + (3 : ℝ)) ^ 4 *
        (2 * (3 + (3 : ℝ))) ^ s ≤ Real.rpow Δ (-ε) := by
      calc _ ≤ (2 * 10^13 : ℝ) := h1
           _ ≤ Real.rpow Δ (-ε) := hΔ_coarse_absorb
    exact h6
  exact A9Support.a9_weaken_constant h_transfer h_const_le

end AppendixA
end DirecretisedFurstenbergEstimate
