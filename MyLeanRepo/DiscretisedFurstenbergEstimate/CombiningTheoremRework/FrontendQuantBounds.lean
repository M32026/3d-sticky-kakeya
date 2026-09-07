module

/-
  Frontend quantitative bound helpers

  Provides standalone lemmas for:
  1. C_P_reg ≤ δ_n^{-(εReg + pointLoss)}
  2. C₁_nat ≤ δ_n^{-(εReg + tubeLoss)}

  The polynomial-in-n factor (K_pigeon = 2n+4) is handled by an
  explicit absorption hypothesis `h_poly_absorb`.

  Whiteprint node: frontend_quantitative_bounds
  Status: COMPLETE
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontendQuantBounds

open DiscretisedFurstenbergEstimate

/-- C_P_reg bound: δ^{-εReg} * 4^u * 9 * (K_pigeon+1) * 4 ≤ δ_n^{-(εReg+pointLoss)}.

    Hypotheses:
    - δ_n ≤ δ/4  (so δ ≥ 4δ_n, hence δ^{-εReg} ≤ δ_n^{-εReg})
    - u ≤ 2  (so 4^u ≤ 16)
    - K_pigeon = 2n + 4
    - h_poly_absorb_half : 1024 * (2n+5) ≤ δ_n^{-pointLoss/2}
      (stronger threshold; full pointLoss follows since δ_n ≤ 1)
-/
lemma C_P_reg_bound {δ δ_n : ℝ} {n : ℕ} {u εReg pointLoss : ℝ}
    (hδn_pos : 0 < δ_n)
    (hδn_leδ4 : δ_n ≤ δ / 4)
    (hεReg_pos : 0 < εReg)
    (hpointLoss_pos : 0 < pointLoss)
    (hu2 : u ≤ 2)
    (hn_ge2 : n ≥ 2)
    (hδn_le_one : δ_n ≤ 1)
    (h_poly_absorb_half : 1024 * (2 * (n : ℝ) + 5) ≤ δ_n^(-pointLoss / 2)) :
    (Real.rpow δ (-εReg)) * (4 : ℝ)^u * 9 * (((2 * n + 4 : ℕ) : ℝ) + 1) * 4 ≤
    δ_n^(-(εReg + pointLoss)) := by
  have hδ_ge : δ_n ≤ δ := by linarith
  have h_neg : -εReg ≤ 0 := by linarith
  have h1 : Real.rpow δ (-εReg) ≤ Real.rpow δ_n (-εReg) :=
    Real.rpow_le_rpow_of_nonpos hδn_pos hδ_ge h_neg
  have h5 : (4 : ℝ)^u ≤ 16 := by
    have h6 : (4 : ℝ)^u ≤ (4 : ℝ)^(2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le <;> norm_num <;> linarith
    norm_num at h6 ⊢ <;> exact h6
  have h6 : (((2 * n + 4 : ℕ) : ℝ) + 1) = 2 * (n : ℝ) + 5 := by
    simp [Nat.cast_add] <;> ring
  have h_half_le_full : δ_n^(-pointLoss / 2) ≤ δ_n^(-pointLoss) :=
    Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_le_one (by linarith)
  have h_poly_absorb : 1024 * (2 * (n : ℝ) + 5) ≤ δ_n^(-pointLoss) :=
    le_trans h_poly_absorb_half h_half_le_full
  have h_pos2 : 0 ≤ (4 : ℝ)^u := by positivity
  have h_pos3 : 0 ≤ (2 * (n : ℝ) + 5) := by positivity
  have h7 : (Real.rpow δ (-εReg)) * (4 : ℝ)^u * 9 * (((2 * n + 4 : ℕ) : ℝ) + 1) * 4 ≤
      δ_n^(-εReg) * (576 * (2 * (n : ℝ) + 5)) := by
    rw [h6]
    calc (Real.rpow δ (-εReg)) * (4 : ℝ)^u * 9 * (2 * (n : ℝ) + 5) * 4
      = (Real.rpow δ (-εReg)) * ((4 : ℝ)^u) * (9 * (2 * (n : ℝ) + 5) * 4) := by ring
    _ ≤ δ_n^(-εReg) * ((4 : ℝ)^u) * (9 * (2 * (n : ℝ) + 5) * 4) := by
          gcongr
          <;> exact h1
    _ ≤ δ_n^(-εReg) * 16 * (9 * (2 * (n : ℝ) + 5) * 4) := by
          have h_pos : 0 ≤ δ_n^(-εReg) * (9 * (2 * (n : ℝ) + 5) * 4) := by positivity
          nlinarith [h5]
    _ = δ_n^(-εReg) * (576 * (2 * (n : ℝ) + 5)) := by ring
  have h7a : δ_n^(-εReg) * (576 * (2 * (n : ℝ) + 5)) ≤
      δ_n^(-εReg) * (1024 * (2 * (n : ℝ) + 5)) := by
    gcongr <;> norm_num
  have h10 : δ_n^(-εReg) * (1024 * (2 * (n : ℝ) + 5)) ≤
      δ_n^(-εReg) * δ_n^(-pointLoss) := by
    gcongr
    <;> exact h_poly_absorb
  have h11 : δ_n^(-εReg) * δ_n^(-pointLoss) = δ_n^(-(εReg + pointLoss)) := by
    have h_exp : -εReg + -pointLoss = -(εReg + pointLoss) := by ring
    rw [← Real.rpow_add hδn_pos, h_exp]
  rw [h11] at h10
  exact le_trans h7 (le_trans h7a h10)

/-- C₁_nat bound: Nat.ceil(C₁_real) ≤ δ_n^{-(εReg+tubeLoss)}.

    Takes C₁_real as an explicit parameter and a hypothesis that
    C₁_real + 1 ≤ δ_n^{-εReg} * K_C1, with K_C1 absorbed by δ_n^{-tubeLoss}.
-/
lemma C₁_bound {δ_n : ℝ} {εReg tubeLoss : ℝ}
    (hδn_pos : 0 < δ_n)
    (hεReg_pos : 0 < εReg)
    (htubeLoss_pos : 0 < tubeLoss)
    (C₁_real K_C1 : ℝ)
    (hC1_real_nonneg : 0 ≤ C₁_real)
    (hK_C1_nonneg : 0 ≤ K_C1)
    (hK_C1_absorb : K_C1 ≤ δ_n^(-tubeLoss))
    (hC1_real_bound : C₁_real + 1 ≤ δ_n^(-εReg) * K_C1) :
    (Nat.ceil C₁_real : ℝ) ≤ δ_n^(-(εReg + tubeLoss)) := by
  have h_ceil : (Nat.ceil C₁_real : ℝ) ≤ C₁_real + 1 := by
    have h : (Nat.ceil C₁_real : ℝ) < C₁_real + 1 := Nat.ceil_lt_add_one hC1_real_nonneg
    exact le_of_lt h
  have h_final : δ_n^(-εReg) * K_C1 ≤ δ_n^(-(εReg + tubeLoss)) := by
    have h1 : δ_n^(-(εReg + tubeLoss)) = δ_n^(-εReg) * δ_n^(-tubeLoss) := by
      have h_exp : -(εReg + tubeLoss) = -εReg + -tubeLoss := by ring
      rw [h_exp, Real.rpow_add hδn_pos]
    rw [h1]
    gcongr <;> exact hK_C1_absorb
  exact le_trans (le_trans h_ceil hC1_real_bound) h_final

/-- Helper to derive C₁_real + 1 ≤ δ_n^{-εReg} * K_C1 from
    C₁_real = K_const * δ^{-εReg} and δ ≥ δ_n. -/
lemma C₁_real_bound_helper {δ δ_n : ℝ} {εReg : ℝ}
    (hδn_pos : 0 < δ_n)
    (hδn_leδ : δ_n ≤ δ)
    (hεReg_pos : 0 < εReg)
    (hδn_le_one : δ_n ≤ 1)
    (K_const K_C1 : ℝ)
    (hK_const_nonneg : 0 ≤ K_const)
    (hK_C1_nonneg : 0 ≤ K_C1)
    (hK : K_const + 1 ≤ K_C1)
    (C₁_real : ℝ)
    (hC1_eq : C₁_real = K_const * Real.rpow δ (-εReg)) :
    C₁_real + 1 ≤ δ_n^(-εReg) * K_C1 := by
  have h_neg : -εReg ≤ 0 := by linarith
  have h1 : Real.rpow δ (-εReg) ≤ Real.rpow δ_n (-εReg) :=
    Real.rpow_le_rpow_of_nonpos hδn_pos hδn_leδ h_neg
  have h2 : C₁_real + 1 = K_const * Real.rpow δ (-εReg) + 1 := by
    rw [hC1_eq] <;> ring
  rw [h2]
  have h3 : K_const * Real.rpow δ (-εReg) ≤ K_const * δ_n^(-εReg) := by
    gcongr
    <;> exact h1
  have h41 : 1 ≤ δ_n^(-εReg) := by
    have h42 : -εReg ≤ 0 := by linarith
    have h43 : δ_n ≤ 1 := hδn_le_one
    have h44 : δ_n^(0 : ℝ) ≤ δ_n^(-εReg) :=
      Real.rpow_le_rpow_of_exponent_ge hδn_pos h43 h42
    simpa using h44
  have h4 : K_const * δ_n^(-εReg) + 1 ≤ (K_const + 1) * δ_n^(-εReg) := by
    have h5 : (K_const + 1) * δ_n^(-εReg) = K_const * δ_n^(-εReg) + δ_n^(-εReg) := by ring
    rw [h5]
    have h6 : K_const * δ_n^(-εReg) + 1 ≤ K_const * δ_n^(-εReg) + δ_n^(-εReg) := by
      gcongr
      <;> exact h41
    exact h6
  calc K_const * Real.rpow δ (-εReg) + 1
    ≤ K_const * δ_n^(-εReg) + 1 := by gcongr <;> exact h1
  _ ≤ (K_const + 1) * δ_n^(-εReg) := h4
  _ ≤ K_C1 * δ_n^(-εReg) := by
    have h8 : (K_const + 1) * δ_n^(-εReg) ≤ K_C1 * δ_n^(-εReg) := by
      gcongr
      <;> exact hK
    exact h8
  _ = δ_n^(-εReg) * K_C1 := by ring

/-- K_P_reg bound: δ^{-εReg} * 4 ≤ δ_n^{-(εReg+pointLoss)}.

    Uses K_point ≥ 4 and K_point ≤ δ^{-pointLoss} ≤ δ_n^{-pointLoss}.
    Requires εReg > 0, pointLoss > 0, δ_n ≤ δ/4, δ_n ≤ 1.
-/
lemma K_P_reg_bound {δ δ_n : ℝ} {n : ℕ} {εReg pointLoss : ℝ}
    (hδn_pos : 0 < δ_n)
    (hδn_leδ4 : δ_n ≤ δ / 4)
    (hεReg_pos : 0 < εReg)
    (hpointLoss_pos : 0 < pointLoss)
    (hδn_le_one : δ_n ≤ 1)
    (K_point : ℝ)
    (hK_point_ge4 : 4 ≤ K_point)
    (hK_point_absorb : K_point ≤ δ^(-pointLoss)) :
    0 ≤ (Real.rpow δ (-εReg)) * 4 ∧
    (Real.rpow δ (-εReg)) * 4 ≤ δ_n^(-(εReg + pointLoss)) := by
  have hδ_pos : 0 < δ := by linarith
  have hδ_ge : δ_n ≤ δ := by linarith
  have h_neg : -εReg ≤ 0 := by linarith
  have h1 : Real.rpow δ (-εReg) ≤ Real.rpow δ_n (-εReg) :=
    Real.rpow_le_rpow_of_nonpos hδn_pos hδ_ge h_neg
  have h2 : (4 : ℝ) ≤ δ_n^(-pointLoss) := by
    have h3 : δ^(-pointLoss) ≤ δ_n^(-pointLoss) :=
      Real.rpow_le_rpow_of_nonpos hδn_pos hδ_ge (by linarith)
    calc (4 : ℝ)
      ≤ K_point := hK_point_ge4
    _ ≤ δ^(-pointLoss) := hK_point_absorb
    _ ≤ δ_n^(-pointLoss) := h3
  have h_pos : 0 ≤ Real.rpow δ (-εReg) * 4 := by
    have h5 : 0 ≤ Real.rpow δ (-εReg) := Real.rpow_nonneg (by linarith) _
    exact mul_nonneg h5 (by norm_num)
  have h_main : Real.rpow δ (-εReg) * 4 ≤ δ_n^(-εReg) * δ_n^(-pointLoss) := by
    calc Real.rpow δ (-εReg) * 4
      ≤ δ_n^(-εReg) * 4 := by gcongr <;> exact h1
    _ ≤ δ_n^(-εReg) * δ_n^(-pointLoss) := by gcongr <;> exact h2
  have h4 : δ_n^(-εReg) * δ_n^(-pointLoss) = δ_n^(-(εReg + pointLoss)) := by
    have h_exp : -εReg + -pointLoss = -(εReg + pointLoss) := by ring
    rw [← Real.rpow_add hδn_pos, h_exp]
  rw [h4] at h_main
  exact ⟨h_pos, h_main⟩

/-- C₁_nat bound via explicit K_C1 absorption.

    C₁_real = K_const * δ^{-εReg}, C₁_nat = Nat.ceil(C₁_real).
    Requires K_const + 1 ≤ K_C1 and K_C1 ≤ δ_n^{-tubeLoss}.
-/
lemma C₁_nat_bound {δ δ_n : ℝ} {εReg tubeLoss : ℝ}
    (hδn_pos : 0 < δ_n)
    (hδn_leδ : δ_n ≤ δ)
    (hεReg_pos : 0 < εReg)
    (htubeLoss_pos : 0 < tubeLoss)
    (hδn_le_one : δ_n ≤ 1)
    (K_const K_C1 : ℝ)
    (hK_const_nonneg : 0 ≤ K_const)
    (hK_C1_nonneg : 0 ≤ K_C1)
    (hK : K_const + 1 ≤ K_C1)
    (hK_C1_absorb : K_C1 ≤ δ_n^(-tubeLoss))
    (C₁_real : ℝ)
    (hC1_nonneg : 0 ≤ C₁_real)
    (hC1_eq : C₁_real = K_const * Real.rpow δ (-εReg)) :
    (Nat.ceil C₁_real : ℝ) ≤ δ_n^(-(εReg + tubeLoss)) := by
  have h_bound : C₁_real + 1 ≤ δ_n^(-εReg) * K_C1 :=
    C₁_real_bound_helper hδn_pos hδn_leδ hεReg_pos hδn_le_one
      K_const K_C1 hK_const_nonneg hK_C1_nonneg hK C₁_real hC1_eq
  exact C₁_bound hδn_pos hεReg_pos htubeLoss_pos C₁_real K_C1
    hC1_nonneg hK_C1_nonneg hK_C1_absorb h_bound

end DirecretisedFurstenbergEstimate.FrontendQuantBounds

end
