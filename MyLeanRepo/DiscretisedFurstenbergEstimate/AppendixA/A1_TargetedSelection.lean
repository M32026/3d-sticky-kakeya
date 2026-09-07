module

/-
  A1 Targeted Selection: Replace dyadic pigeonholing + stub 3.

  Selects heavy coarse squares with threshold m₀ = Δ^{-t+3ε},
  then takes a subset of size ≈ Δ^{-t+3ε} to satisfy both
  lower and upper cardinality bounds.

  Internal budgeting (relaxed ball-growth constant Δ^{-9ε/4}):
  - Pfin extraction uses ε/4 loss (card bounds)
  - Per-square upper U = Δ^{-t-5ε/2} ≤ Δ^{-t-3ε}
  - Threshold m₀ = Δ^{-t+3ε}
  - N·m₀ ≤ Δ^{-2t+5ε/2} ≤ T/2 (since Δ^{9ε/4} ≤ 1/512)
  - H ≥ T/(2U) = Δ^{-t+11ε/4}/2 ≥ Δ^{-t+3ε} (since Δ^{-ε/4} ≥ 2)

  Hypothesis hN_cover (occupied squares bound) is left as an assumption
  for now; to be proved via tube incidence double-counting.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Support
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section


namespace DirecretisedFurstenbergEstimate.Cobalt

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareSet squareCenter point_in_square_close_to_center)
open DirecretisedFurstenbergEstimate.Phase2 (squareIndex point_in_own_square squareIndex_unique)

local notation "Plane" => EuclideanPlane

attribute [local instance] Classical.propDecidable

/-- Helper: Δ^{-t+ε} + 1 ≤ Δ^{-t-ε} under small-Δ condition. -/
lemma targeted_selection_upper_bound (Δ t ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε) (ht : 0 < t) (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 2) :
    Real.rpow Δ (-t + ε) + 1 ≤ Real.rpow Δ (-t - ε) := by
  have h_rpow_mul : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b; exact (Real.rpow_add hΔ_pos a b).symm
  have h4 : Real.rpow Δ (-ε / 4) ≥ 2 := by
    have h5 : Real.rpow Δ (ε / 4) * Real.rpow Δ (-ε / 4) = 1 := by
      have h := h_rpow_mul (ε / 4) (-ε / 4)
      have h6 : (ε / 4 : ℝ) + (-ε / 4) = 0 := by ring
      rw [h6] at h; simpa using h
    have h6 : Real.rpow Δ (-ε / 4) = (Real.rpow Δ (ε / 4))⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right h5).symm
    rw [h6]
    have h_pos1 : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h10 : 1 / Real.rpow Δ (ε / 4) ≥ 2 := by
      calc 1 / Real.rpow Δ (ε / 4)
        ≥ 1 / (1 / 2 : ℝ) := by gcongr
      _ = 2 := by norm_num
    simpa using h10
  have h6 : Real.rpow Δ (-ε / 2) ≥ 4 := by
    have h7 : Real.rpow Δ (ε / 2) * Real.rpow Δ (-ε / 2) = 1 := by
      have h := h_rpow_mul (ε / 2) (-ε / 2)
      have h8 : (ε / 2 : ℝ) + (-ε / 2) = 0 := by ring
      rw [h8] at h; simpa using h
    have h8 : Real.rpow Δ (-ε / 2) = (Real.rpow Δ (ε / 2))⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right h7).symm
    rw [h8]
    have h2 : Real.rpow Δ (ε / 2) ≤ 1 / 4 := by
      have h3 : Real.rpow Δ (ε / 2) = Real.rpow Δ (ε / 4) * Real.rpow Δ (ε / 4) := by
        rw [h_rpow_mul (ε / 4) (ε / 4)] <;> ring_nf
      rw [h3]
      have h_pos : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
      nlinarith [h_small, h_pos]
    have h_pos2 : 0 < Real.rpow Δ (ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
    have h10 : 1 / Real.rpow Δ (ε / 2) ≥ 4 := by
      calc 1 / Real.rpow Δ (ε / 2)
        ≥ 1 / (1 / 4 : ℝ) := by gcongr
      _ = 4 := by norm_num
    simpa using h10
  have h15 : Real.rpow Δ (-2 * ε) ≥ 4 := by
    have h16 : Real.rpow Δ (-ε / 2) * Real.rpow Δ (-ε / 2) = Real.rpow Δ (-ε) := by
      rw [h_rpow_mul (-ε / 2) (-ε / 2)] <;> ring_nf
    have h17 : Real.rpow Δ (-ε) * Real.rpow Δ (-ε) = Real.rpow Δ (-2 * ε) := by
      rw [h_rpow_mul (-ε) (-ε)] <;> ring_nf
    have h18 : Real.rpow Δ (-2 * ε) = (Real.rpow Δ (-ε / 2)) ^ 4 := by
      calc Real.rpow Δ (-2 * ε)
        = Real.rpow Δ (-ε) * Real.rpow Δ (-ε) := h17.symm
      _ = (Real.rpow Δ (-ε / 2) * Real.rpow Δ (-ε / 2)) * (Real.rpow Δ (-ε / 2) * Real.rpow Δ (-ε / 2)) := by rw [h16] <;> ring
      _ = (Real.rpow Δ (-ε / 2)) ^ 4 := by ring
    rw [h18]
    have h19 : Real.rpow Δ (-ε / 2) ≥ 4 := h6
    have h20 : (Real.rpow Δ (-ε / 2)) ^ 4 ≥ 4 := by
      have h21 : (Real.rpow Δ (-ε / 2)) ^ 4 ≥ 4 ^ 4 := by gcongr
      have h22 : (4 : ℝ) ^ 4 ≥ 4 := by norm_num
      linarith
    exact h20
  by_cases h_case : t ≥ ε
  · -- t ≥ ε: x ≥ 1, y = x * Δ^{-2ε} ≥ 4x ≥ x+1
    have h25 : -t + ε ≤ 0 := by linarith
    set x := Real.rpow Δ (-t + ε) with hx
    have h24 : x ≥ 1 := by
      have h26 : Real.rpow Δ 0 ≤ Real.rpow Δ (-t + ε) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h25
      have h27 : Real.rpow Δ 0 = 1 := by simp
      rw [h27] at h26
      exact h26
    have h28 : Real.rpow Δ (-2 * ε) ≥ 4 := h15
    have h23 : Real.rpow Δ (-t - ε) = x * Real.rpow Δ (-2 * ε) := by
      rw [h_rpow_mul (-t + ε) (-2 * ε)] <;> ring_nf
    rw [h23]
    have hx_pos : 0 ≤ x := by positivity
    have hxy1 : x * Real.rpow Δ (-2 * ε) ≥ 4 * x := by
      have h : x * Real.rpow Δ (-2 * ε) ≥ x * 4 := mul_le_mul_of_nonneg_left h28 hx_pos
      have h2 : x * 4 = 4 * x := by ring
      rw [h2] at h; exact h
    have hxy2 : 4 * x ≥ x + 1 := by
      have h_x_ge1 : x ≥ 1 := h24
      linarith
    calc x * Real.rpow Δ (-2 * ε)
        ≥ 4 * x := hxy1
      _ ≥ x + 1 := hxy2
  · -- t < ε: Δ^{-t-ε} ≥ 2, Δ^{-t+ε} < 1, so x + 1 < 2 ≤ Δ^{-t-ε}
    have h_t_lt_eps : t < ε := by linarith
    have h24 : (ε / 4 : ℝ) ≤ t + ε := by linarith
    have h25 : Real.rpow Δ (t + ε) ≤ Real.rpow Δ (ε / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h24
    have h26 : Real.rpow Δ (t + ε) ≤ 1 / 2 := le_trans h25 h_small
    have h27 : 0 < Real.rpow Δ (t + ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h28 : Real.rpow Δ (-t - ε) ≥ 2 := by
      have h_sum : (t + ε) + (-t - ε) = 0 := by ring
      have h29 : Real.rpow Δ (t + ε) * Real.rpow Δ (-t - ε) = 1 := by
        have h := h_rpow_mul (t + ε) (-t - ε)
        rw [h_sum] at h
        simpa using h
      have h30 : Real.rpow Δ (-t - ε) = 1 / Real.rpow Δ (t + ε) := by
        have h31 : Real.rpow Δ (t + ε) * Real.rpow Δ (-t - ε) = 1 := h29
        field_simp [h27.ne'] <;> linarith
      rw [h30]
      have h31 : 1 / Real.rpow Δ (t + ε) ≥ 2 := by
        calc 1 / Real.rpow Δ (t + ε)
          ≥ 1 / (1 / 2 : ℝ) := by gcongr
        _ = 2 := by norm_num
      exact h31
    have h32 : Real.rpow Δ (-t + ε) < 1 := by
      have h33 : -t + ε > 0 := by linarith
      exact Real.rpow_lt_one (by linarith) (by linarith) (by linarith)
    have h34 : Real.rpow Δ (-t + ε) + 1 < 2 := by linarith
    have h35 : (2 : ℝ) ≤ Real.rpow Δ (-t - ε) := h28
    exact le_of_lt (lt_of_lt_of_le h34 h35)

/-- Generalized upper bound: Δ^{-t+3ε} + 1 ≤ Δ^{-t-3ε} under Δ^{ε/4} ≤ 1/2. -/
lemma targeted_selection_upper_bound_3ε (Δ t ε : ℝ) (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hε_pos : 0 < ε) (ht : 0 < t) (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 2) :
    Real.rpow Δ (-t + 3 * ε) + 1 ≤ Real.rpow Δ (-t - 3 * ε) := by
  have h_rpow_mul : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b; exact (Real.rpow_add hΔ_pos a b).symm
  have h4 : Real.rpow Δ (-ε / 4) ≥ 2 := by
    have h5 : Real.rpow Δ (ε / 4) * Real.rpow Δ (-ε / 4) = 1 := by
      have h := h_rpow_mul (ε / 4) (-ε / 4)
      have h6 : (ε / 4 : ℝ) + (-ε / 4) = 0 := by ring
      rw [h6] at h; simpa using h
    have h6 : Real.rpow Δ (-ε / 4) = (Real.rpow Δ (ε / 4))⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right h5).symm
    rw [h6]
    have h_pos1 : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h10 : 1 / Real.rpow Δ (ε / 4) ≥ 2 := by
      calc 1 / Real.rpow Δ (ε / 4)
        ≥ 1 / (1 / 2 : ℝ) := by gcongr
      _ = 2 := by norm_num
    simpa using h10
  have h_neg6ε : Real.rpow Δ (-6 * ε) ≥ 4 := by
    have h_eq1 : (-6 * ε : ℝ) = (-ε / 4) * 24 := by ring
    rw [h_eq1]
    have h2 : Real.rpow Δ ((-ε / 4) * 24) = (Real.rpow Δ (-ε / 4)) ^ 24 := by
      simpa using Real.rpow_mul_natCast hΔ_pos.le (-ε / 4) 24
    rw [h2]
    have h3 : (Real.rpow Δ (-ε / 4)) ^ 24 ≥ (2 : ℝ) ^ 24 := by gcongr
    have h4' : (2 : ℝ) ^ 24 ≥ 4 := by norm_num
    linarith
  by_cases h_case : t ≥ 3 * ε
  · -- t ≥ 3ε: x ≥ 1, y = x * Δ^{-6ε} ≥ 4x ≥ x+1
    have h25 : -t + 3 * ε ≤ 0 := by linarith
    set x := Real.rpow Δ (-t + 3 * ε) with hx
    have h24 : x ≥ 1 := by
      have h26 : Real.rpow Δ 0 ≤ Real.rpow Δ (-t + 3 * ε) :=
        Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h25
      have h27 : Real.rpow Δ 0 = 1 := by simp
      rw [h27] at h26
      exact h26
    have h23 : Real.rpow Δ (-t - 3 * ε) = x * Real.rpow Δ (-6 * ε) := by
      rw [h_rpow_mul (-t + 3 * ε) (-6 * ε)] <;> ring_nf
    rw [h23]
    have hx_pos : 0 ≤ x := by positivity
    have hxy1 : x * Real.rpow Δ (-6 * ε) ≥ 4 * x := by
      have h : x * Real.rpow Δ (-6 * ε) ≥ x * 4 := mul_le_mul_of_nonneg_left h_neg6ε hx_pos
      have h2 : x * 4 = 4 * x := by ring
      rw [h2] at h; exact h
    have hxy2 : 4 * x ≥ x + 1 := by
      have h_x_ge1 : x ≥ 1 := h24
      linarith
    calc x * Real.rpow Δ (-6 * ε)
        ≥ 4 * x := hxy1
      _ ≥ x + 1 := hxy2
  · -- t < 3ε: Δ^{-t-3ε} ≥ 2, Δ^{-t+3ε} < 1, so x + 1 < 2 ≤ Δ^{-t-3ε}
    have h_t_lt : t < 3 * ε := by linarith
    have h24 : (ε / 4 : ℝ) ≤ t + 3 * ε := by linarith
    have h25 : Real.rpow Δ (t + 3 * ε) ≤ Real.rpow Δ (ε / 4) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_lt_one.le h24
    have h26 : Real.rpow Δ (t + 3 * ε) ≤ 1 / 2 := le_trans h25 h_small
    have h27 : 0 < Real.rpow Δ (t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h28 : Real.rpow Δ (-t - 3 * ε) ≥ 2 := by
      have h_sum : (t + 3 * ε) + (-t - 3 * ε) = 0 := by ring
      have h29 : Real.rpow Δ (t + 3 * ε) * Real.rpow Δ (-t - 3 * ε) = 1 := by
        have h := h_rpow_mul (t + 3 * ε) (-t - 3 * ε)
        rw [h_sum] at h; simpa using h
      have h30 : Real.rpow Δ (-t - 3 * ε) = 1 / Real.rpow Δ (t + 3 * ε) := by
        field_simp [h27.ne'] <;> linarith
      rw [h30]
      have h31 : 1 / Real.rpow Δ (t + 3 * ε) ≥ 2 := by
        calc 1 / Real.rpow Δ (t + 3 * ε)
          ≥ 1 / (1 / 2 : ℝ) := by gcongr
        _ = 2 := by norm_num
      exact h31
    have h32 : Real.rpow Δ (-t + 3 * ε) < 1 := by
      have h33 : -t + 3 * ε > 0 := by linarith
      exact Real.rpow_lt_one (by linarith) (by linarith) (by linarith)
    have h34 : Real.rpow Δ (-t + 3 * ε) + 1 < 2 := by linarith
    have h35 : (2 : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := h28
    exact le_of_lt (lt_of_lt_of_le h34 h35)

/-- Targeted heavy-square selection with final cardinality bounds.
    Takes Pfin with relaxed ball-growth (Δ^{-9ε/4}), outputs Qset with ±3ε bounds. -/
lemma a1_targeted_selection
    {Δ t ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (ht : 0 < t) (hε_pos : 0 < ε)
    (Pfin : Finset Plane)
    (hP_card_lower : Real.rpow Δ (-2 * t + ε / 4) ≤ (Pfin.card : ℝ))
    (hP_card_upper : (Pfin.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4))
    (hP_ball_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * (Pfin.card : ℝ))
    (hN_cover : ∀ (Q_all : Finset (ℤ × ℤ)),
      Q_all = Pfin.image (fun p => squareIndex Δ p) →
      (Q_all.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2))
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 2) :
    ∃ (Qset : Finset (ℤ × ℤ)),
      (Real.rpow Δ (-t + 3 * ε) ≤ (Qset.card : ℝ)) ∧
      ((Qset.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε)) ∧
      (∀ Q ∈ Qset,
        Real.rpow Δ (-t + 3 * ε) ≤ ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ∧
        ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε)) := by
  have hΔ_lt_one : Δ < 1 := by linarith

  -- Helper for rpow arithmetic
  have h_rpow_mul : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b
    exact (Real.rpow_add hΔ_pos a b).symm
  have h_rpow_div : ∀ (a b : ℝ), Real.rpow Δ a / Real.rpow Δ b = Real.rpow Δ (a - b) := by
    intro a b
    have h : Real.rpow Δ (a - b) = Real.rpow Δ a / Real.rpow Δ b := Real.rpow_sub hΔ_pos a b
    exact h.symm
  have h_rpow_le_iff : ∀ (a b : ℝ), Real.rpow Δ a ≤ Real.rpow Δ b ↔ b ≤ a := by
    intro a b
    constructor
    · intro h
      by_contra h2
      have h3 : a < b := by linarith
      have h4 : Real.rpow Δ b < Real.rpow Δ a := by
        apply Real.rpow_lt_rpow_of_exponent_gt <;> linarith
      linarith
    · intro h
      exact Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) h

  -- Small Δ consequences
  have h1 : Real.rpow Δ (ε / 4) ≤ 1 / 2 := h_small
  have h2 : Real.rpow Δ (ε / 2) ≤ 1 / 4 := by
    have h3 : Real.rpow Δ (ε / 2) = Real.rpow Δ (ε / 4) * Real.rpow Δ (ε / 4) := by
      rw [h_rpow_mul (ε / 4) (ε / 4)] <;> ring_nf
    rw [h3]
    have h_pos : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    nlinarith [h1, h_pos]
  have h4 : Real.rpow Δ (-ε / 4) ≥ 2 := by
    have h51 : (ε / 4 : ℝ) + (-ε / 4) = 0 := by ring
    have h5 : Real.rpow Δ (ε / 4) * Real.rpow Δ (-ε / 4) = 1 := by
      have h := h_rpow_mul (ε / 4) (-ε / 4)
      rw [h51] at h
      simpa using h
    have h6 : Real.rpow Δ (-ε / 4) = (Real.rpow Δ (ε / 4))⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right h5).symm
    rw [h6]
    have h_pos1 : 0 < Real.rpow Δ (ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
    have h_ge : (Real.rpow Δ (ε / 4))⁻¹ ≥ 2 := by
      have h9 : (Real.rpow Δ (ε / 4))⁻¹ = 1 / Real.rpow Δ (ε / 4) := by simp
      rw [h9]
      have h10 : 1 / Real.rpow Δ (ε / 4) ≥ 2 := by
        calc 1 / Real.rpow Δ (ε / 4)
          ≥ 1 / (1 / 2 : ℝ) := by gcongr
        _ = 2 := by norm_num
      exact h10
    exact h_ge
  have h6 : Real.rpow Δ (-ε / 2) ≥ 4 := by
    have h71 : (ε / 2 : ℝ) + (-ε / 2) = 0 := by ring
    have h7 : Real.rpow Δ (ε / 2) * Real.rpow Δ (-ε / 2) = 1 := by
      have h := h_rpow_mul (ε / 2) (-ε / 2)
      rw [h71] at h
      simpa using h
    have h8 : Real.rpow Δ (-ε / 2) = (Real.rpow Δ (ε / 2))⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right h7).symm
    rw [h8]
    have h_pos2 : 0 < Real.rpow Δ (ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
    have h_ge : (Real.rpow Δ (ε / 2))⁻¹ ≥ 4 := by
      have h9 : (Real.rpow Δ (ε / 2))⁻¹ = 1 / Real.rpow Δ (ε / 2) := by simp
      rw [h9]
      have h10 : 1 / Real.rpow Δ (ε / 2) ≥ 4 := by
        calc 1 / Real.rpow Δ (ε / 2)
          ≥ 1 / (1 / 4 : ℝ) := by gcongr
        _ = 4 := by norm_num
      exact h10
    exact h_ge

  let Q_all : Finset (ℤ × ℤ) := Pfin.image (fun p => squareIndex Δ p)
  let n : (ℤ × ℤ) → ℕ := fun Q => (Pfin.filter (fun p => p ∈ squareSet Δ Q)).card

  -- Total points = sum over occupied squares
  have h_cover : ∀ p ∈ Pfin, p ∈ squareSet Δ (squareIndex Δ p) :=
    fun p _ => point_in_own_square hΔ_pos p
  have h_disj : ∀ (Q1 Q2 : ℤ × ℤ), Q1 ≠ Q2 →
      Disjoint (Pfin.filter (fun p => p ∈ squareSet Δ Q1))
        (Pfin.filter (fun p => p ∈ squareSet Δ Q2)) := by
    intro Q1 Q2 hne
    simp only [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p ∈ squareSet Δ Q1 := (Finset.mem_filter.mp hp1).2
    have h2 : p ∈ squareSet Δ Q2 := (Finset.mem_filter.mp hp2).2
    have hx11 : Δ * (Q1.1 : ℝ) ≤ p 0 := h1.1.1
    have hx12 : p 0 < Δ * ((Q1.1 : ℝ) + 1) := h1.1.2
    have hx21 : Δ * (Q2.1 : ℝ) ≤ p 0 := h2.1.1
    have hx22 : p 0 < Δ * ((Q2.1 : ℝ) + 1) := h2.1.2
    have h3 : Q1.1 = Q2.1 := by
      by_contra hne2
      have h_lt : Q1.1 < Q2.1 ∨ Q2.1 < Q1.1 := by omega
      rcases h_lt with (h_lt | h_lt)
      · have h_ineq1 : (Q1.1 : ℝ) + 1 ≤ (Q2.1 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q1.1 : ℝ) + 1) ≤ Δ * (Q2.1 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q1.1 : ℝ) + 1) ≤ p 0 := by linarith [hx21]
        exact False.elim (not_le.mpr hx12 h_ineq3)
      · have h_ineq1 : (Q2.1 : ℝ) + 1 ≤ (Q1.1 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q2.1 : ℝ) + 1) ≤ Δ * (Q1.1 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q2.1 : ℝ) + 1) ≤ p 0 := by linarith [hx11]
        exact False.elim (not_le.mpr hx22 h_ineq3)
    have hy11 : Δ * (Q1.2 : ℝ) ≤ p 1 := h1.2.1
    have hy12 : p 1 < Δ * ((Q1.2 : ℝ) + 1) := h1.2.2
    have hy21 : Δ * (Q2.2 : ℝ) ≤ p 1 := h2.2.1
    have hy22 : p 1 < Δ * ((Q2.2 : ℝ) + 1) := h2.2.2
    have h4 : Q1.2 = Q2.2 := by
      by_contra hne2
      have h_lt : Q1.2 < Q2.2 ∨ Q2.2 < Q1.2 := by omega
      rcases h_lt with (h_lt | h_lt)
      · have h_ineq1 : (Q1.2 : ℝ) + 1 ≤ (Q2.2 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q1.2 : ℝ) + 1) ≤ Δ * (Q2.2 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q1.2 : ℝ) + 1) ≤ p 1 := by linarith [hy21]
        exact False.elim (not_le.mpr hy12 h_ineq3)
      · have h_ineq1 : (Q2.2 : ℝ) + 1 ≤ (Q1.2 : ℝ) := by exact_mod_cast (by omega)
        have h_ineq2 : Δ * ((Q2.2 : ℝ) + 1) ≤ Δ * (Q1.2 : ℝ) := by gcongr
        have h_ineq3 : Δ * ((Q2.2 : ℝ) + 1) ≤ p 1 := by linarith [hy11]
        exact False.elim (not_le.mpr hy22 h_ineq3)
    have h5 : Q1 = Q2 := by ext <;> tauto
    exact hne h5
  have h_disj' : Set.PairwiseDisjoint (Q_all : Set (ℤ × ℤ)) (fun Q => Pfin.filter (fun p => p ∈ squareSet Δ Q)) := by
    intro Q1 hQ1 Q2 hQ2 hne
    exact h_disj Q1 Q2 hne
  have h_sum : ∑ Q ∈ Q_all, n Q = Pfin.card := by
    have h_biUnion : Q_all.biUnion (fun Q => Pfin.filter (fun p => p ∈ squareSet Δ Q)) = Pfin := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨Q, _, hp, _⟩
        exact hp
      · intro hp
        let Q := squareIndex Δ p
        have hQ : Q ∈ Q_all := by
          exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
        have hpin : p ∈ squareSet Δ Q := h_cover p hp
        exact ⟨Q, hQ, hp, hpin⟩
    have h_card : ∑ Q ∈ Q_all, n Q = (Q_all.biUnion (fun Q => Pfin.filter (fun p => p ∈ squareSet Δ Q))).card := by
      rw [Finset.card_biUnion h_disj'] <;> rfl
    have h_main : (Q_all.biUnion (fun Q => Pfin.filter (fun p => p ∈ squareSet Δ Q))).card = Pfin.card := by
      rw [h_biUnion]
    rw [h_card, h_main]

  let m₀ : ℝ := Real.rpow Δ (-t + 3 * ε)
  have hm₀_pos : 0 < m₀ := Real.rpow_pos_of_pos hΔ_pos _

  -- Per-square upper bound U = Δ^{-t-5ε/2}
  let U : ℝ := Real.rpow Δ (-t - 5 * ε / 2)
  have hU_pos : 0 < U := Real.rpow_pos_of_pos hΔ_pos _
  have h_per_square_upper : ∀ Q ∈ Q_all, (n Q : ℝ) ≤ U := by
    intro Q hQ
    let c := squareCenter Δ Q
    have h1 : (Pfin.filter (fun p => p ∈ squareSet Δ Q)) ⊆
        Pfin.filter (fun y => dist c y ≤ Δ) := by
      intro p hp
      have hp' : p ∈ squareSet Δ Q := (Finset.mem_filter.mp hp).2
      have hdist : dist p c ≤ Real.sqrt 2 * Δ / 2 :=
        Lagoon.point_in_square_close_to_center hΔ_pos Q p hp'
      have h2 : Real.sqrt 2 * Δ / 2 ≤ Δ := by
        have h3 : Real.sqrt 2 / 2 ≤ 1 := by
          have h4 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
          linarith
        nlinarith
      have h3 : dist c p ≤ Δ := by
        rw [dist_comm] <;> linarith
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, h3⟩
    have h4 : (n Q : ℝ) ≤ ((Pfin.filter (fun y => dist c y ≤ Δ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h1
    have h5 := hP_ball_growth c Δ (by linarith)
    have h6 : ((Pfin.filter (fun y => dist c y ≤ Δ)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * Δ^t * (Pfin.card : ℝ) := h5
    have h7 : Real.rpow Δ (-9 * ε / 4) * Δ^t * (Pfin.card : ℝ) ≤ U := by
      have h8 : (Pfin.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4) := hP_card_upper
      have h9 : Real.rpow Δ (-9 * ε / 4) * Δ^t * (Pfin.card : ℝ) ≤
          Real.rpow Δ (-9 * ε / 4) * Δ^t * Real.rpow Δ (-2 * t - ε / 4) := by
        have hpos1 : 0 ≤ Real.rpow Δ (-9 * ε / 4) := Real.rpow_nonneg hΔ_pos.le _
        have hpos2 : 0 ≤ (Δ ^ t) := by positivity
        have hpos : 0 ≤ Real.rpow Δ (-9 * ε / 4) * Δ^t := mul_nonneg hpos1 hpos2
        gcongr <;> linarith
      have h10 : Real.rpow Δ (-9 * ε / 4) * Δ^t * Real.rpow Δ (-2 * t - ε / 4) = U := by
        have h11 : Real.rpow Δ (-9 * ε / 4) * (Δ ^ t) = Real.rpow Δ (t - 9 * ε / 4) := by
          change Real.rpow Δ (-9 * ε / 4) * Real.rpow Δ t = Real.rpow Δ (t - 9 * ε / 4)
          rw [h_rpow_mul (-9 * ε / 4) t] <;> ring_nf
        rw [h11]
        have h12 : Real.rpow Δ (t - 9 * ε / 4) * Real.rpow Δ (-2 * t - ε / 4) =
            Real.rpow Δ (-t - 5 * ε / 2) := by
          rw [h_rpow_mul (t - 9 * ε / 4) (-2 * t - ε / 4)] <;> ring_nf
        rw [h12] <;> rfl
      rw [h10] at h9
      exact h9
    exact le_trans h4 (le_trans h6 h7)

  -- N bound
  have hN : (Q_all.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2) := hN_cover Q_all rfl

  -- Heavy squares
  let heavy : Finset (ℤ × ℤ) := Q_all.filter (fun Q => m₀ ≤ (n Q : ℝ))
  let light : Finset (ℤ × ℤ) := Q_all.filter (fun Q => (n Q : ℝ) < m₀)

  have h_light_upper : ∀ Q ∈ light, (n Q : ℝ) < m₀ := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).2
  have h_heavy_lower : ∀ Q ∈ heavy, m₀ ≤ (n Q : ℝ) := by
    intro Q hQ
    exact (Finset.mem_filter.mp hQ).2

  -- Total points = light + heavy
  have h_partition : ∑ Q ∈ Q_all, (n Q : ℝ) =
      ∑ Q ∈ light, (n Q : ℝ) + ∑ Q ∈ heavy, (n Q : ℝ) := by
    have h_sub : light ∪ heavy ⊆ Q_all := by
      intro Q hQ
      rcases Finset.mem_union.mp hQ with (h | h)
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
    have h_sub2 : Q_all ⊆ light ∪ heavy := by
      intro Q hQ
      by_cases hcase : m₀ ≤ (n Q : ℝ)
      · have hh : Q ∈ heavy := Finset.mem_filter.mpr ⟨hQ, hcase⟩
        exact Finset.mem_union.mpr (Or.inr hh)
      · have hlt : (n Q : ℝ) < m₀ := lt_of_not_ge hcase
        have hh : Q ∈ light := Finset.mem_filter.mpr ⟨hQ, hlt⟩
        exact Finset.mem_union.mpr (Or.inl hh)
    have h1 : light ∪ heavy = Q_all := Finset.Subset.antisymm h_sub h_sub2
    have h2 : Disjoint light heavy := by
      simp only [Finset.disjoint_left, Finset.mem_filter]
      intro Q h1 h2
      have h3 : (n Q : ℝ) < m₀ := (Finset.mem_filter.mp h1).2
      have h4 : m₀ ≤ (n Q : ℝ) := (Finset.mem_filter.mp h2).2
      linarith
    rw [← Finset.sum_union h2, h1]
  have hT : (Pfin.card : ℝ) = ∑ Q ∈ Q_all, (n Q : ℝ) := by
    have h : (∑ Q ∈ Q_all, (n Q : ℝ)) = (Pfin.card : ℝ) := by exact_mod_cast h_sum
    exact h.symm
  have h_light_sum : ∑ Q ∈ light, (n Q : ℝ) ≤ (light.card : ℝ) * m₀ := by
    have h3 : ∀ Q ∈ light, (n Q : ℝ) ≤ m₀ := by
      intro Q hQ
      have h4 : (n Q : ℝ) < m₀ := h_light_upper Q hQ
      linarith
    calc
      ∑ Q ∈ light, (n Q : ℝ) ≤ ∑ Q ∈ light, m₀ := Finset.sum_le_sum h3
      _ = (light.card : ℝ) * m₀ := by simp [Finset.sum_const] <;> ring
  have h_heavy_sum : ∑ Q ∈ heavy, (n Q : ℝ) ≤ (heavy.card : ℝ) * U := by
    have h3 : ∀ Q ∈ heavy, (n Q : ℝ) ≤ U := by
      intro Q hQ
      have hQ' : Q ∈ Q_all := (Finset.mem_filter.mp hQ).1
      exact h_per_square_upper Q hQ'
    calc
      ∑ Q ∈ heavy, (n Q : ℝ) ≤ ∑ Q ∈ heavy, U := Finset.sum_le_sum h3
      _ = (heavy.card : ℝ) * U := by simp [Finset.sum_const] <;> ring

  -- T ≤ light_sum + heavy_sum ≤ N_light · m₀ + H · U ≤ N · m₀ + H · U
  have h_main_ineq : (Pfin.card : ℝ) ≤ (Q_all.card : ℝ) * m₀ + (heavy.card : ℝ) * U := by
    have h4 : (light.card : ℝ) ≤ (Q_all.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    calc (Pfin.card : ℝ)
        = ∑ Q ∈ Q_all, (n Q : ℝ) := hT
      _ = ∑ Q ∈ light, (n Q : ℝ) + ∑ Q ∈ heavy, (n Q : ℝ) := h_partition
      _ ≤ (light.card : ℝ) * m₀ + (heavy.card : ℝ) * U := by gcongr
      _ ≤ (Q_all.card : ℝ) * m₀ + (heavy.card : ℝ) * U := by gcongr

  -- N · m₀ ≤ Δ^{-t-ε/2} · Δ^{-t+3ε} = Δ^{-2t+5ε/2}
  have hN_m₀ : (Q_all.card : ℝ) * m₀ ≤ Real.rpow Δ (-2 * t + 5 * ε / 2) := by
    have h5 : (Q_all.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2) := hN
    have h6 : 0 ≤ (Q_all.card : ℝ) := by positivity
    have h7 : (Q_all.card : ℝ) * m₀ ≤ Real.rpow Δ (-t - ε / 2) * m₀ := by gcongr
    have h8 : Real.rpow Δ (-t - ε / 2) * m₀ = Real.rpow Δ (-2 * t + 5 * ε / 2) := by
      simp only [m₀]
      rw [h_rpow_mul (-t - ε / 2) (-t + 3 * ε)] <;> ring_nf
    rw [h8] at h7
    exact h7

  -- T ≥ Δ^{-2t+ε/4}
  have hT_lower : (Pfin.card : ℝ) ≥ Real.rpow Δ (-2 * t + ε / 4) := hP_card_lower

  -- N · m₀ ≤ T / 2  (from h_small: Δ^{ε/4} ≤ 1/2, so Δ^{9ε/4} ≤ 1/512 ≤ 1/2)
  have hN_m₀_half : (Q_all.card : ℝ) * m₀ ≤ (Pfin.card : ℝ) / 2 := by
    have h9 : Real.rpow Δ (-2 * t + 5 * ε / 2) ≤ Real.rpow Δ (-2 * t + ε / 4) / 2 := by
      have h10 : Real.rpow Δ (-2 * t + 5 * ε / 2) =
          Real.rpow Δ (9 * ε / 4) * Real.rpow Δ (-2 * t + ε / 4) := by
        rw [h_rpow_mul (9 * ε / 4) (-2 * t + ε / 4)] <;> ring_nf
      rw [h10]
      have h11 : 0 < Real.rpow Δ (-2 * t + ε / 4) := Real.rpow_pos_of_pos hΔ_pos _
      have h12 : Real.rpow Δ (9 * ε / 4) ≤ 1 / 2 := by
        have h_eq : (9 * ε / 4 : ℝ) = (ε / 4) * 9 := by ring
        have h13 : Real.rpow Δ (9 * ε / 4) = (Real.rpow Δ (ε / 4)) ^ 9 := by
          rw [h_eq]
          exact Real.rpow_mul_natCast hΔ_pos.le (ε / 4) 9
        rw [h13]
        have h14 : (Real.rpow Δ (ε / 4)) ^ 9 ≤ (1 / 2 : ℝ) ^ 9 := by
          have h_a_nonneg : 0 ≤ Real.rpow Δ (ε / 4) := Real.rpow_nonneg hΔ_pos.le _
          have h_mono : ∀ n : ℕ, (Real.rpow Δ (ε / 4)) ^ n ≤ (1 / 2 : ℝ) ^ n := by
            intro n
            induction n with
            | zero => norm_num
            | succ n ih =>
              calc (Real.rpow Δ (ε / 4)) ^ (n + 1)
                = (Real.rpow Δ (ε / 4)) ^ n * Real.rpow Δ (ε / 4) := by ring
              _ ≤ (1 / 2 : ℝ) ^ n * Real.rpow Δ (ε / 4) := by
                exact mul_le_mul_of_nonneg_right ih h_a_nonneg
              _ ≤ (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) := by
                gcongr
                <;> exact h_small
              _ = (1 / 2 : ℝ) ^ (n + 1) := by ring
          exact h_mono 9
        have h15 : (1 / 2 : ℝ) ^ 9 ≤ 1 / 2 := by norm_num
        exact le_trans h14 h15
      nlinarith [h_small]
    calc (Q_all.card : ℝ) * m₀
      ≤ Real.rpow Δ (-2 * t + 5 * ε / 2) := hN_m₀
    _ ≤ Real.rpow Δ (-2 * t + ε / 4) / 2 := h9
    _ ≤ (Pfin.card : ℝ) / 2 := by gcongr

  -- H ≥ (T - N·m₀) / U ≥ T / (2U)
  have hH_lower1 : (heavy.card : ℝ) ≥ (Pfin.card : ℝ) / (2 * U) := by
    have h_pos : 0 < U := hU_pos
    have h : (Pfin.card : ℝ) ≤ (Q_all.card : ℝ) * m₀ + (heavy.card : ℝ) * U := h_main_ineq
    have h2 : (Pfin.card : ℝ) - (Q_all.card : ℝ) * m₀ ≤ (heavy.card : ℝ) * U := by linarith
    have h3 : (Pfin.card : ℝ) / 2 ≤ (Pfin.card : ℝ) - (Q_all.card : ℝ) * m₀ := by linarith [hN_m₀_half]
    have h4 : (Pfin.card : ℝ) / 2 ≤ (heavy.card : ℝ) * U := by linarith
    have h5 : (Pfin.card : ℝ) / (2 * U) ≤ (heavy.card : ℝ) := by
      calc (Pfin.card : ℝ) / (2 * U)
        = ((Pfin.card : ℝ) / 2) / U := by ring
      _ ≤ ((heavy.card : ℝ) * U) / U := by gcongr
      _ = (heavy.card : ℝ) := by
        have h_div : ((heavy.card : ℝ) * U) / U = (heavy.card : ℝ) := by
          rw [mul_div_cancel_right₀ (heavy.card : ℝ) h_pos.ne']
        exact h_div
    exact h5

  -- H ≥ Δ^{-t+11ε/4} / 2 ≥ Δ^{-t+3ε}  (since Δ^{-ε/4} ≥ 2)
  have hH_lower2 : (heavy.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε) := by
    have h_posU : 0 < U := hU_pos
    have h61 : Real.rpow Δ (-2 * t + ε / 4) ≤ (Pfin.card : ℝ) := hP_card_lower
    have h6 : (Pfin.card : ℝ) / (2 * U) ≥ Real.rpow Δ (-2 * t + ε / 4) / (2 * U) := by
      exact div_le_div_of_nonneg_right h61 (by positivity)
    have h7 : Real.rpow Δ (-2 * t + ε / 4) / (2 * U) =
        Real.rpow Δ (-t + 11 * ε / 4) / 2 := by
      dsimp only [U]
      have h8 : Real.rpow Δ (-2 * t + ε / 4) / Real.rpow Δ (-t - 5 * ε / 2) =
          Real.rpow Δ (-t + 11 * ε / 4) := by
        rw [h_rpow_div (-2 * t + ε / 4) (-t - 5 * ε / 2)]
        congr 1
        <;> ring
      have h9 : Real.rpow Δ (-2 * t + ε / 4) / (2 * Real.rpow Δ (-t - 5 * ε / 2)) =
          (Real.rpow Δ (-2 * t + ε / 4) / Real.rpow Δ (-t - 5 * ε / 2)) / 2 := by ring
      rw [h9, h8] <;> ring
    have h9 : (heavy.card : ℝ) ≥ Real.rpow Δ (-t + 11 * ε / 4) / 2 := by
      calc (heavy.card : ℝ)
        ≥ (Pfin.card : ℝ) / (2 * U) := hH_lower1
      _ ≥ Real.rpow Δ (-2 * t + ε / 4) / (2 * U) := h6
      _ = Real.rpow Δ (-t + 11 * ε / 4) / 2 := h7
    have h10 : Real.rpow Δ (-t + 11 * ε / 4) / 2 ≥ Real.rpow Δ (-t + 3 * ε) := by
      have h11 : Real.rpow Δ (-t + 11 * ε / 4) = Real.rpow Δ (-ε / 4) * Real.rpow Δ (-t + 3 * ε) := by
        rw [h_rpow_mul (-ε / 4) (-t + 3 * ε)]
        congr 1
        <;> ring
      rw [h11]
      set x := Real.rpow Δ (-t + 3 * ε) with hx
      have h12 : 0 < x := Real.rpow_pos_of_pos hΔ_pos _
      have h13 : Real.rpow Δ (-ε / 4) ≥ 2 := h4
      have h14 : Real.rpow Δ (-ε / 4) * x ≥ 2 * x := by
        gcongr <;> linarith
      have h15 : (Real.rpow Δ (-ε / 4) * x) / 2 ≥ x := by linarith
      exact h15
    have h_final : (heavy.card : ℝ) ≥ Real.rpow Δ (-t + 3 * ε) := by
      calc (heavy.card : ℝ)
        ≥ Real.rpow Δ (-t + 11 * ε / 4) / 2 := h9
      _ ≥ Real.rpow Δ (-t + 3 * ε) := h10
    exact h_final

  -- Need heavy.Nonempty
  have h_heavy_nonempty : heavy.Nonempty := by
    have h13 : 0 < Real.rpow Δ (-t + 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h14 : 0 < (heavy.card : ℝ) := by linarith [hH_lower2]
    exact Finset.card_pos.mp (by exact_mod_cast h14)

  -- Select subset of size ceil(Δ^{-t+3ε})
  let target : ℕ := Nat.ceil (Real.rpow Δ (-t + 3 * ε))
  have h_target_ge : (target : ℝ) ≥ Real.rpow Δ (-t + 3 * ε) := by
    exact Nat.le_ceil _
  have h_target_le_heavy : target ≤ heavy.card := by
    exact Nat.ceil_le.mpr hH_lower2
  rcases Finset.exists_subset_card_eq h_target_le_heavy with ⟨Qset, hQset_sub, hQset_card⟩

  -- |Qset| = target
  have hQset_card_eq : (Qset.card : ℝ) = (target : ℝ) := by
    exact_mod_cast hQset_card

  -- Lower bound: |Qset| ≥ Δ^{-t+3ε}
  have hQset_lower : Real.rpow Δ (-t + 3 * ε) ≤ (Qset.card : ℝ) := by
    rw [hQset_card_eq]
    exact h_target_ge

  -- Upper bound: |Qset| ≤ Δ^{-t-3ε}
  -- Need target ≤ Δ^{-t-3ε}, i.e., ceil(x) ≤ y where x = Δ^{-t+3ε}, y = Δ^{-t-3ε}
  -- It suffices to show x + 1 ≤ y
  have h_upper1 : Real.rpow Δ (-t + 3 * ε) + 1 ≤ Real.rpow Δ (-t - 3 * ε) :=
    targeted_selection_upper_bound_3ε Δ t ε hΔ_pos hΔ_lt_one hε_pos ht h_small
  have hQset_upper : (Qset.card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := by
    have h_pos : 0 ≤ Real.rpow Δ (-t + 3 * ε) := by positivity
    have h25 : (target : ℝ) < Real.rpow Δ (-t + 3 * ε) + 1 := Nat.ceil_lt_add_one h_pos
    have h26 : (target : ℝ) ≤ Real.rpow Δ (-t + 3 * ε) + 1 := le_of_lt h25
    rw [hQset_card_eq]
    exact le_trans h26 h_upper1

  -- Per-square bounds for Qset
  have h_points_lower : ∀ Q ∈ Qset,
      Real.rpow Δ (-t + 3 * ε) ≤ ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) := by
    intro Q hQ
    have hQ_heavy : Q ∈ heavy := hQset_sub hQ
    have h26 : m₀ ≤ (n Q : ℝ) := h_heavy_lower Q hQ_heavy
    simpa [m₀] using h26
  have h_points_upper : ∀ Q ∈ Qset,
      ((Pfin.filter (fun p => p ∈ squareSet Δ Q)).card : ℝ) ≤ Real.rpow Δ (-t - 3 * ε) := by
    intro Q hQ
    have hQ_heavy : Q ∈ heavy := hQset_sub hQ
    have hQ_all : Q ∈ Q_all := (Finset.mem_filter.mp hQ_heavy).1
    have h27 : (n Q : ℝ) ≤ U := h_per_square_upper Q hQ_all
    have h28 : U ≤ Real.rpow Δ (-t - 3 * ε) := by
      dsimp only [U]
      rw [h_rpow_le_iff] <;> linarith
    exact le_trans h27 h28

  exact ⟨Qset, hQset_lower, hQset_upper,
    fun Q hQ => ⟨h_points_lower Q hQ, h_points_upper Q hQ⟩⟩

end DirecretisedFurstenbergEstimate.Cobalt
