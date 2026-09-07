import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridParameterSelectionHelpers

/-!
# Large-base terminal-grid parameters for tube-parameter OS tree

Choose the grid base after `eta`, then choose a terminal level at each small
scale.  The exact-cell fiber logarithm costs one half of `delta^{-eta}` and
the four-dimensional local OS branching loss costs the other half.
-/

namespace Kakeya.Assouad

theorem tube_parameter_grid_parameter_selection :
    TubeParameterGridParameterSelectionStatement := by
  intro eta heta

  -- Step 1: large base with C_nat ≤ base^(eta/2)
  rcases exists_large_base4 (eta / 2) (by linarith) with
    ⟨base, hbase_ge3, hC_le⟩
  let C_nat : ℕ := 2 * (Nat.log 2 ((base + 1) ^ 4) + 1)
  let C_real : ℝ := C_nat
  have hC_real_pos : 0 < C_real := by positivity
  have hbase_pos : 0 < (base : ℝ) := by positivity
  have hbase_nonneg : 0 ≤ (base : ℝ) := by linarith
  have hbase1 : 1 < (base : ℝ) := by
    exact_mod_cast (show 1 < base from by omega)
  have hC_le' : C_real ≤ (base : ℝ) ^ (eta / 2) := by
    simpa [C_real, C_nat] using hC_le

  -- Step 2: log absorption constant
  let K_log : ℝ := 3 / Real.log 2 + 1
  let K' : ℝ := 2 * K_log
  have hK'_pos : 0 < K' := by positivity
  have heta2_pos : 0 < eta / 2 := by linarith

  rcases exists_delta_log_absorbed (n := 1) K' hK'_pos heta2_pos (by norm_num) with
    ⟨δ₀, hδ₀_pos, hδ₀_le1, h_absorb⟩
  let δ₀' : ℝ := min δ₀ (1 / 2)
  have hδ₀'_pos : 0 < δ₀' := by positivity
  have hδ₀'_lt1 : δ₀' < 1 := by
    have h : δ₀' ≤ 1 / 2 := min_le_right _ _
    linarith
  have h_absorb' : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀' →
      K' * (1 + Real.log δ⁻¹) ≤ Real.rpow δ (-(eta / 2)) := by
    intro δ hδ hδ_le
    have h : δ ≤ δ₀ := hδ_le.trans (min_le_left _ _)
    have h9 := h_absorb δ hδ h
    simpa using h9

  refine ⟨base, hbase_ge3, δ₀', hδ₀'_pos, hδ₀'_lt1, ?_⟩
  intro δ hδ hδ_le activeCard h_activeCard

  have hδ_lt1 : δ < 1 := hδ_le.trans_lt hδ₀'_lt1
  rcases exists_levels_mesh base hbase_ge3 δ hδ hδ_lt1 with
    ⟨levels, hmesh1, hmesh2⟩

  -- Step 3: base^levels ≤ δ⁻¹
  have h_base_pow_le : (base : ℝ) ^ levels ≤ δ⁻¹ := by
    have hpos : 0 < (base ^ levels : ℝ) := by positivity
    have h2 : (base ^ levels : ℝ) ≤ δ⁻¹ := by
      calc
        (base ^ levels : ℝ)
            = (((base ^ levels : ℝ)⁻¹)⁻¹) := by
              field_simp [hpos.ne']
        _ ≤ δ⁻¹ := by gcongr
    exact h2

  -- Step 4: C_real^levels ≤ δ^(-eta/2)
  have hC_pow_le :
      C_real ^ levels ≤ Real.rpow δ (-(eta / 2)) := by
    have h1 : C_real ≤ (base : ℝ) ^ (eta / 2) := hC_le'
    have h2 :
        C_real ^ levels ≤ ((base : ℝ) ^ (eta / 2)) ^ levels := by
      gcongr <;> linarith
    have h3 :
        ((base : ℝ) ^ (eta / 2)) ^ levels =
          (base : ℝ) ^ ((eta / 2) * (levels : ℝ)) := by
      have h31 :
          ((base : ℝ) ^ (eta / 2)) ^ (levels : ℝ) =
            (base : ℝ) ^ ((eta / 2) * (levels : ℝ)) := by
        rw [← Real.rpow_mul hbase_nonneg] <;> ring
      have h32 :
          ((base : ℝ) ^ (eta / 2)) ^ levels =
            ((base : ℝ) ^ (eta / 2)) ^ (levels : ℝ) := by
        rw [Real.rpow_natCast]
      rw [h32, h31]
    rw [h3] at h2
    have h4 :
        (base : ℝ) ^ ((eta / 2) * (levels : ℝ)) =
          (base : ℝ) ^ ((levels : ℝ) * (eta / 2)) := by ring_nf
    rw [h4] at h2
    have h51 :
        (base : ℝ) ^ ((levels : ℝ) * (eta / 2)) =
          ((base : ℝ) ^ (levels : ℝ)) ^ (eta / 2) :=
      Real.rpow_mul hbase_nonneg (levels : ℝ) (eta / 2)
    have h52 :
        (base : ℝ) ^ (levels : ℝ) = (base : ℝ) ^ levels := by
      rw [Real.rpow_natCast]
    have h5 :
        (base : ℝ) ^ ((levels : ℝ) * (eta / 2)) =
          ((base : ℝ) ^ levels) ^ (eta / 2) := by
      rw [h51, h52]
    rw [h5] at h2
    have h6 :
        ((base : ℝ) ^ levels) ^ (eta / 2) ≤ (δ⁻¹) ^ (eta / 2) :=
      Real.rpow_le_rpow (by positivity) h_base_pow_le (by linarith)
    have h7 : (δ⁻¹) ^ (eta / 2) = Real.rpow δ (-(eta / 2)) :=
      Eq.symm (Real.rpow_neg_eq_inv_rpow δ (eta / 2))
    rw [h7] at h6
    exact h2.trans h6

  -- Step 5: activeCard log bound
  have h_log_bound :
      (Nat.log 2 activeCard + 1 : ℝ) ≤
        K_log * (1 + Real.log δ⁻¹) :=
    active_card_log_bound activeCard δ hδ hδ_lt1.le h_activeCard

  -- Step 6: combine in ℝ
  have h_absorb_δ :
      K' * (1 + Real.log δ⁻¹) ≤ Real.rpow δ (-(eta / 2)) :=
    h_absorb' δ hδ hδ_le

  have h_rpow2_nonneg : 0 ≤ Real.rpow δ (-(eta / 2)) :=
    Real.rpow_nonneg hδ.le (-(eta / 2))

  have h_product_real :
      ((Nat.log 2 activeCard + 1 : ℝ) * (2 : ℝ) * C_real ^ levels) ≤
        Real.rpow δ (-eta) := by
    have h1 :
        ((Nat.log 2 activeCard + 1 : ℝ) * (2 : ℝ) * C_real ^ levels) ≤
          (K_log * (1 + Real.log δ⁻¹)) * (2 : ℝ) * C_real ^ levels := by
      gcongr <;> linarith
    have h2 :
        (K_log * (1 + Real.log δ⁻¹)) * (2 : ℝ) * C_real ^ levels =
          K' * (1 + Real.log δ⁻¹) * C_real ^ levels := by
      dsimp only [K', K_log] <;> ring
    rw [h2] at h1
    have h3 :
        K' * (1 + Real.log δ⁻¹) * C_real ^ levels ≤
          K' * (1 + Real.log δ⁻¹) * Real.rpow δ (-(eta / 2)) := by
      gcongr <;> linarith [h_rpow2_nonneg]
    have h4 :
        K' * (1 + Real.log δ⁻¹) * Real.rpow δ (-(eta / 2)) ≤
          Real.rpow δ (-(eta / 2)) * Real.rpow δ (-(eta / 2)) := by
      have h41 : K' * (1 + Real.log δ⁻¹) ≤ Real.rpow δ (-(eta / 2)) := h_absorb_δ
      have h42 : 0 ≤ Real.rpow δ (-(eta / 2)) := h_rpow2_nonneg
      nlinarith
    have h5 :
        Real.rpow δ (-(eta / 2)) * Real.rpow δ (-(eta / 2)) =
          Real.rpow δ (-eta) := by
      have h_rpow :
          Real.rpow δ (-(eta / 2)) * Real.rpow δ (-(eta / 2)) =
            Real.rpow δ ((-(eta / 2)) + (-(eta / 2))) :=
          (Real.rpow_add hδ (-(eta / 2)) (-(eta / 2))).symm
      rw [h_rpow]
      have h6 : (-(eta / 2)) + (-(eta / 2)) = -eta := by ring
      rw [h6]
    rw [h5] at h4
    exact h1.trans (h3.trans h4)

  -- Step 7: transfer to ENNReal
  let x : ℕ := Nat.log 2 activeCard + 1
  let y : ℕ := 2
  let z : ℕ := C_nat ^ levels
  have h_main3 : ∀ (a b c : ℕ),
      (↑a : ENNReal) * (↑b : ENNReal) * (↑c : ENNReal) =
      ENNReal.ofReal ((a : ℝ) * (b : ℝ) * (c : ℝ)) := by
    intro a b c
    have h1 : (↑a : ENNReal) * (↑b : ENNReal) * (↑c : ENNReal) = ↑(a * b * c) := by
      rw [← Nat.cast_mul, ← Nat.cast_mul] <;> rfl
    rw [h1]
    have h2 : (↑(a * b * c) : ENNReal) = ENNReal.ofReal (↑(a * b * c) : ℝ) := by
      exact (ENNReal.ofReal_natCast (a * b * c)).symm
    rw [h2]
    have h3 : (↑(a * b * c) : ℝ) = (a : ℝ) * (b : ℝ) * (c : ℝ) := by
      simp [Nat.cast_mul] <;> ring
    rw [h3]
  have h_goal :
      tubeParameterGridInitialLoss activeCard base levels =
        (↑x : ENNReal) * (↑y : ENNReal) * (↑z : ENNReal) := by
    unfold tubeParameterGridInitialLoss
    dsimp only [x, y, z, C_nat]
    have h_eq1 : (↑(Nat.log 2 activeCard) + 1 : ENNReal) = ↑(Nat.log 2 activeCard + 1) := by
      norm_cast
    rw [h_eq1] <;> rfl
  have h_r :
      (x : ℝ) * (y : ℝ) * (z : ℝ) =
        (Nat.log 2 activeCard + 1 : ℝ) * (2 : ℝ) * C_real ^ levels := by
    simp [x, y, z, C_real, Nat.cast_pow] <;> norm_cast
  have h_cast_loss :
      tubeParameterGridInitialLoss activeCard base levels =
        ENNReal.ofReal ((Nat.log 2 activeCard + 1 : ℝ) * (2 : ℝ) * C_real ^ levels) := by
    rw [h_goal, h_main3 x y z, h_r]

  exact ⟨levels, hmesh1, hmesh2, by
    rw [h_cast_loss]
    exact ENNReal.ofReal_mono h_product_real⟩

end Kakeya.Assouad
