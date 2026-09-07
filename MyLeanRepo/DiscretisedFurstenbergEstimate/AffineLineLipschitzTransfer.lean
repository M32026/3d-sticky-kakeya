module

/-
  Lipschitz transfer lemmas for AffineLine ↔ ℝ×ℝ parameter space.

  Provides:
  - offset_norm_le_abs_b: ‖offset‖ ≤ |b|
  - affineLineParams_lipschitz_upper: dist(params) ≤ 8 * dist(line)

  The antilipschitz bound (dist(line) ≤ K * dist(params)) is proved below
  using:
  1. Projection e₁ formula: P e₁ = a • P e₂
  2. Operator norm bound: ‖P₁-P₂‖ ≤ 3|Δa| (via ‖T‖ ≤ ‖T e₁‖ + ‖T e₂‖)
  3. Offset vector norm bound: ‖off₁-off₂‖ ≤ |Δb| + 2|Δa| (via algebraic identity)
  Combined: dist(line) ≤ 3|Δa| + |Δb| + 2|Δa| ≤ 6·dist(params)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate
open LemmaE

noncomputable section

namespace AffineLineLipschitzTransfer

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Norm bound on offset: ‖ℓ.offset‖ ≤ |b|. -/
lemma offset_norm_le_abs_b (ℓ : AffineLine) (hv1 : (getDirV ℓ) 1 ≠ 0) :
    ‖ℓ.offset‖ ≤ |(affineLineParams ℓ).2| := by
  set a := (affineLineParams ℓ).1 with ha_def
  set b := (affineLineParams ℓ).2 with hb_def
  have h_formula := TubesAndSlopes.offset_formula ℓ hv1
  have h_off0 : ℓ.offset 0 = b / (1 + a^2) := h_formula.1
  have h_off1 : ℓ.offset 1 = -a * b / (1 + a^2) := h_formula.2
  have h_pos : 0 < 1 + a^2 := by positivity
  have h_norm_sq : ‖ℓ.offset‖ ^ 2 = (ℓ.offset 0)^2 + (ℓ.offset 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
  have h_main : ‖ℓ.offset‖ ^ 2 = b^2 / (1 + a^2) := by
    rw [h_norm_sq, h_off0, h_off1]
    field_simp [h_pos.ne'] <;> ring
  have h51 : 1 ≤ 1 + a^2 := by nlinarith
  have h4 : ‖ℓ.offset‖ ^ 2 ≤ b^2 := by
    rw [h_main]
    have h5 : b^2 / (1 + a^2) ≤ b^2 := by
      apply div_le_self (by positivity) h51
    exact h5
  have h6 : 0 ≤ ‖ℓ.offset‖ := by positivity
  have h7 : 0 ≤ |b| := by positivity
  have h8 : ‖ℓ.offset‖ ^ 2 ≤ (|b|) ^ 2 := by
    have h9 : b^2 = (|b|)^2 := by rw [sq_abs]
    rw [h9] at h4
    exact h4
  have h10 : ‖ℓ.offset‖ ≤ |b| := by
    nlinarith [Real.sqrt_nonneg (‖ℓ.offset‖ ^ 2)]
  exact h10

/-- Forward Lipschitz: dist(params) ≤ 8 * dist(line). -/
lemma affineLineParams_lipschitz_upper
    (ℓ₁ ℓ₂ : AffineLine)
    (hv1 : (getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (getDirV ℓ₂) 1 ≠ 0)
    (ha1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (ha2 : |(affineLineParams ℓ₂).1| ≤ 1)
    (hb1 : |(affineLineParams ℓ₁).2| ≤ 3)
    (hb2 : |(affineLineParams ℓ₂).2| ≤ 3) :
    dist (affineLineParams ℓ₁) (affineLineParams ℓ₂) ≤ 8 * dist ℓ₁ ℓ₂ := by
  set a1 := (affineLineParams ℓ₁).1 with ha1_def
  set a2 := (affineLineParams ℓ₂).1 with ha2_def
  set b1 := (affineLineParams ℓ₁).2 with hb1_def
  set b2 := (affineLineParams ℓ₂).2 with hb2_def
  set d := dist ℓ₁ ℓ₂ with hd_def
  set o := ‖ℓ₁.offset - ℓ₂.offset‖ with ho_def
  set p := ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ with hp_def
  have h_p_nonneg : 0 ≤ p := norm_nonneg _
  have h_o_le_d : o ≤ d := by
    have h : d = p + o := by simp [AffineLine.dist, ho_def, hp_def] <;> rfl
    linarith [h_p_nonneg]
  have h_a : |a1 - a2| ≤ 2 * d :=
    TubesAndSlopes.slope_lipschitz ℓ₁ ℓ₂ hv1 hv2 ha1 ha2
  have hb1_eq : b1 = ℓ₁.offset 0 - a1 * ℓ₁.offset 1 := by
    simp [affineLineParams, ha1_def, hb1_def, hv1] <;> aesop
  have hb2_eq : b2 = ℓ₂.offset 0 - a2 * ℓ₂.offset 1 := by
    simp [affineLineParams, ha2_def, hb2_def, hv2] <;> aesop
  have h_off2_1 : |ℓ₂.offset 1| ≤ 3 := by
    have h : |ℓ₂.offset 1| ≤ ‖ℓ₂.offset‖ := TubesAndSlopes.coord_abs_le_norm ℓ₂.offset 1
    have h2 : ‖ℓ₂.offset‖ ≤ |b2| := offset_norm_le_abs_b ℓ₂ hv2
    exact le_trans h (le_trans h2 hb2)
  have h_off0_diff : |ℓ₁.offset 0 - ℓ₂.offset 0| ≤ o :=
    TubesAndSlopes.coord_abs_le_norm (ℓ₁.offset - ℓ₂.offset) 0
  have h_off1_diff : |ℓ₁.offset 1 - ℓ₂.offset 1| ≤ o :=
    TubesAndSlopes.coord_abs_le_norm (ℓ₁.offset - ℓ₂.offset) 1
  have h_d_nonneg : 0 ≤ d := dist_nonneg
  have h_b : |b1 - b2| ≤ 8 * d := by
    rw [hb1_eq, hb2_eq]
    set x := ℓ₁.offset 0 - ℓ₂.offset 0 with hx_def
    set y := a1 * (ℓ₁.offset 1 - ℓ₂.offset 1) + (a1 - a2) * ℓ₂.offset 1 with hy_def
    have h_alg : (ℓ₁.offset 0 - a1 * ℓ₁.offset 1) - (ℓ₂.offset 0 - a2 * ℓ₂.offset 1) = x - y := by
      simp [hx_def, hy_def] <;> ring
    rw [h_alg]
    have h_abs1 : |x - y| ≤ |x| + |y| := by exact abs_sub x y
    have h_abs2 : |y| ≤ |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := by
      have h : |y| ≤ |a1 * (ℓ₁.offset 1 - ℓ₂.offset 1)| + |(a1 - a2) * ℓ₂.offset 1| := by exact abs_add_le (a1 * (ℓ₁.offset.ofLp 1 - ℓ₂.offset.ofLp 1)) ((a1 - a2) * ℓ₂.offset.ofLp 1)
      have h2 : |a1 * (ℓ₁.offset 1 - ℓ₂.offset 1)| = |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| := by rw [abs_mul]
      have h3 : |(a1 - a2) * ℓ₂.offset 1| = |a1 - a2| * |ℓ₂.offset 1| := by rw [abs_mul]
      linarith
    have h_tri : |x - y| ≤ |x| + |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := by
      linarith [h_abs1, h_abs2]
    calc |x - y|
      ≤ |x| + |a1| * |ℓ₁.offset 1 - ℓ₂.offset 1| + |a1 - a2| * |ℓ₂.offset 1| := h_tri
    _ ≤ o + 1 * o + (2 * d) * 3 := by gcongr <;> linarith [ha1, h_off0_diff, h_off1_diff, h_a, h_off2_1]
    _ = 2 * o + 6 * d := by ring
    _ ≤ 2 * d + 6 * d := by gcongr
    _ = 8 * d := by ring
  have h_goal_a : |a1 - a2| ≤ 8 * d := by
    have h : |a1 - a2| ≤ 2 * d := h_a
    have h2 : 2 * d ≤ 8 * d := by linarith [h_d_nonneg]
    linarith
  have h_main : dist (a1, b1) (a2, b2) ≤ 8 * d := by
    simp only [Prod.dist_eq, max_le_iff]
    exact ⟨h_goal_a, h_b⟩
  exact h_main

/-- Antilipschitz bound: dist(line) ≤ 10 * dist(params).

    PROOF SKETCH (not yet formalized):
    Let Δa = |a₁-a₂|, Δb = |b₁-b₂|, dp = dist(params) = max(Δa, Δb).

    1. Projection difference:
       - P e₁ = a • P e₂ (since e₁ - a•e₂ is orthogonal to direction)
       - (P₁-P₂) e₁ = a₁•(P₁-P₂)e₂ + (a₁-a₂)•P₂e₂
       - ‖(P₁-P₂)e₂‖ = Δa / √((1+a₁²)(1+a₂²)) ≤ Δa
       - ‖P₂e₂‖ ≤ 1, |a₁| ≤ 1
       - ‖(P₁-P₂)e₁‖ ≤ 2Δa
       - ‖P₁-P₂‖ ≤ ‖(P₁-P₂)e₁‖ + ‖(P₁-P₂)e₂‖ ≤ 3Δa

    2. Offset difference (decompose by varying b then a):
       - Varying b: norm ≤ Δb (since norm² = Δb²/(1+a₁²) ≤ Δb²)
       - Varying a: norm² = b₂²·Δa²·[(a₁+a₂)²+(1-a₁a₂)²] / D²
                  = b₂²·Δa²/D ≤ 4Δa² (using identity (a₁+a₂)²+(1-a₁a₂)² = D)
         so norm ≤ 2Δa
       - Total: ‖off₁-off₂‖ ≤ Δb + 2Δa ≤ 3dp

    3. Combined: dist(line) = ‖P₁-P₂‖ + ‖off₁-off₂‖ ≤ 3Δa + 3dp ≤ 6dp ≤ 10dp
-/
lemma affineLineParams_antilipschitz
    (ℓ₁ ℓ₂ : AffineLine)
    (hv1 : (getDirV ℓ₁) 1 ≠ 0)
    (hv2 : (getDirV ℓ₂) 1 ≠ 0)
    (ha1 : |(affineLineParams ℓ₁).1| ≤ 1)
    (ha2 : |(affineLineParams ℓ₂).1| ≤ 1)
    (hb1 : |(affineLineParams ℓ₁).2| ≤ 3)
    (hb2 : |(affineLineParams ℓ₂).2| ≤ 3) :
    dist ℓ₁ ℓ₂ ≤ 10 * dist (affineLineParams ℓ₁) (affineLineParams ℓ₂) := by
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
  have h_dp_nonneg : 0 ≤ dp := by positivity

  -- Step 1: Projection bound
  have h_proj : ‖ℓ₁.1.direction.starProjection - ℓ₂.1.direction.starProjection‖ ≤
      2 * |a1 - a2| :=
    TubesAndSlopes.direction_proj_upper_bound ℓ₁ ℓ₂ hv1 hv2

  -- Step 2: Offset bound
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

  -- Step 3: Combine
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
  _ ≤ 10 * dp := by linarith [h_dp_nonneg]

end AffineLineLipschitzTransfer
