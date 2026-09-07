module

/-
  CXBound.lean

  Prove that for τ < εF and sufficiently small r, the explicit C_X constant
  from measure_extract_delta_set_explicit satisfies:
    C_X * D_X ≤ (2r)^(-εF)
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-- For any K > 0, ε > 0, p > 0, there exists r₀ > 0 such that for all 0 < r < r₀,
    K * r^p ≤ ε. Also returns explicit definition r₀ = (ε/K)^(1/p). -/
lemma exists_rpow_small (K ε : ℝ) (hK_pos : 0 < K) (hε_pos : 0 < ε) {p : ℝ} (hp_pos : 0 < p) :
    ∃ (r₀ : ℝ), 0 < r₀ ∧ r₀ = Real.rpow (ε / K) (1 / p) ∧
      ∀ (r : ℝ), 0 < r → r < r₀ → K * Real.rpow r p ≤ ε := by
  let q : ℝ := ε / K
  have hq_pos : 0 < q := div_pos hε_pos hK_pos
  let r₀ : ℝ := Real.rpow q (1 / p)
  have hr₀_pos : 0 < r₀ := Real.rpow_pos_of_pos hq_pos (1 / p)
  have hp_ne_zero : (1 / p) ≠ 0 := by
    have h : 0 < 1 / p := by positivity
    exact h.ne'
  have h_inv : (1 / p)⁻¹ = p := by
    field_simp [hp_pos.ne'] <;> ring
  have h_rpow_p : Real.rpow r₀ p = q := by
    have h1 : Real.rpow r₀ p = Real.rpow (Real.rpow q (1 / p)) p := by rfl
    rw [h1]
    have h2 : Real.rpow (Real.rpow q (1 / p)) p =
        Real.rpow (Real.rpow q (1 / p)) ((1 / p)⁻¹) := by rw [h_inv]
    rw [h2]
    exact Real.rpow_rpow_inv hq_pos.le hp_ne_zero
  refine ⟨r₀, hr₀_pos, by rfl, fun r hr_pos hr_lt => ?_⟩
  have h4 : Real.rpow r p ≤ Real.rpow r₀ p :=
    Real.rpow_le_rpow hr_pos.le hr_lt.le hp_pos.le
  have h5 : K * Real.rpow r p ≤ K * Real.rpow r₀ p := by gcongr
  rw [h_rpow_p] at h5
  have h6 : K * q = ε := by
    dsimp only [q]
    field_simp [hK_pos.ne'] <;> ring
  rw [h6] at h5
  exact h5

/-- Helper: (1/r)^a = r^(-a) for r > 0. -/
lemma inv_rpow_eq {r a : ℝ} (hr_pos : 0 < r) :
    (1 / r) ^ a = Real.rpow r (-a) := by
  have h1 : 0 < 1 / r := by positivity
  have h2 : Real.log ((1 / r) ^ a) = a * Real.log (1 / r) := by
    rw [Real.log_rpow h1]
  have h3 : Real.log (1 / r) = - Real.log r := by
    rw [Real.log_div (by norm_num) hr_pos.ne'] <;> simp
  have h4 : Real.log ((1 / r) ^ a) = Real.log (Real.rpow r (-a)) := by
    rw [h2, h3]
    have h5 : a * (-Real.log r) = (-a) * Real.log r := by ring
    rw [h5]
    have h61 : Real.log (r ^ (-a)) = (-a) * Real.log r := Real.log_rpow hr_pos (-a)
    have h6 : Real.log (Real.rpow r (-a)) = (-a) * Real.log r := by
      simpa using h61
    exact h6.symm
  have h7 : 0 < (1 / r) ^ a := Real.rpow_pos_of_pos h1 a
  have h8 : 0 < Real.rpow r (-a) := Real.rpow_pos_of_pos hr_pos (-a)
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr h7) (Set.mem_Ioi.mpr h8) h4

/-- Explicit threshold for the C_X bound.
This is the exact value constructed by `C_X_bound_for_small_r`. -/
noncomputable def c_x_r_ext (τ εF C : ℝ) (D_X : ℕ) : ℝ :=
  let δ : ℝ := εF - τ
  let a : ℝ := δ / 2
  let A : ℝ := Real.log (4000 * C) + 1
  let B : ℝ := (τ + 1) / a
  let K1 : ℝ := 200 * C * (D_X : ℝ) * A
  let K2 : ℝ := 200 * C * (D_X : ℝ) * B
  let target : ℝ := Real.rpow 2 (-εF)
  let p1 : ℝ := εF - τ
  let p2 : ℝ := εF - τ - a
  min (Real.rpow ((target / 2) / K1) (1 / p1))
    (min (Real.rpow ((target / 2) / K2) (1 / p2)) 1)

/-- The C_X bound holds for sufficiently small r. -/
lemma C_X_bound_for_small_r
    (τ εF C : ℝ) (hτ : 0 < τ) (hεF_pos : 0 < εF) (hτ_lt_εF : τ < εF)
    (hC_ge_one : 1 ≤ C) (D_X : ℕ) (hD_X_pos : 0 < D_X) :
    ∃ (r₀ : ℝ), 0 < r₀ ∧ r₀ = c_x_r_ext τ εF C D_X ∧ ∀ (r : ℝ), 0 < r → r < r₀ →
      let m := Real.rpow r τ / 2
      let L := max 0 (Real.log (2000 * C / (m * r))) + 1
      let C_X := 100 * C * L / m
      C_X * (D_X : ℝ) ≤ Real.rpow (2 * r) (-εF) := by
  have hC_pos : 0 < C := by linarith
  set δ : ℝ := εF - τ with hδ_def
  have hδ_pos : 0 < δ := by linarith
  set a : ℝ := δ / 2 with ha_def
  have ha_pos : 0 < a := by linarith

  have h_log4000C_pos : 0 < Real.log (4000 * C) := by
    have h1 : 4000 * C > 1 := by linarith
    have h2 : Real.log (4000 * C) > Real.log 1 := Real.log_lt_log (by positivity) h1
    simpa using h2

  -- For r < 1, log(1/r) ≤ r^(-a)/a
  have h_log_bound : ∀ (r : ℝ), 0 < r → r < 1 →
      Real.log (1 / r) ≤ Real.rpow r (-a) / a := by
    intro r hr_pos hr_lt_one
    have hx_pos : (0 : ℝ) ≤ 1 / r := by positivity
    have h : Real.log (1 / r) ≤ (1 / r) ^ a / a := Real.log_le_rpow_div hx_pos ha_pos
    rw [inv_rpow_eq hr_pos] at h
    exact h

  -- log(2000*C/(m*r)) = log(4000*C) + (τ+1)*log(1/r)
  have h_log_expr : ∀ (r : ℝ), 0 < r →
      Real.log (2000 * C / ((Real.rpow r τ / 2) * r)) =
        Real.log (4000 * C) + (τ + 1) * Real.log (1 / r) := by
    intro r hr_pos
    have h_rpow_add : Real.rpow r (τ + 1) = Real.rpow r τ * r := by
      have h21 : Real.rpow r (τ + 1) = Real.rpow r τ * Real.rpow r (1 : ℝ) := by
        exact Real.rpow_add hr_pos τ (1 : ℝ)
      have h3 : Real.rpow r (1 : ℝ) = r := Real.rpow_one r
      rw [h21, h3] <;> ring
    have h4 : (Real.rpow r τ / 2) * r = Real.rpow r (τ + 1) / 2 := by
      calc (Real.rpow r τ / 2) * r
        = (Real.rpow r τ * r) / 2 := by ring
      _ = Real.rpow r (τ + 1) / 2 := by rw [h_rpow_add]
    have h_pos1 : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr_pos τ
    have h_pos2 : 0 < Real.rpow r (τ + 1) := Real.rpow_pos_of_pos hr_pos (τ + 1)
    have h5 : Real.log (2000 * C / ((Real.rpow r τ / 2) * r)) =
        Real.log (2000 * C) - Real.log ((Real.rpow r τ / 2) * r) := by
      rw [Real.log_div (by positivity) (mul_pos (div_pos h_pos1 (by norm_num)) hr_pos).ne']
    rw [h5]
    have h6 : Real.log ((Real.rpow r τ / 2) * r) =
        Real.log (Real.rpow r (τ + 1)) - Real.log 2 := by
      rw [h4]
      rw [Real.log_div (by positivity) (by norm_num)] <;> ring
    rw [h6]
    have h71 : Real.log (r ^ (τ + 1)) = (τ + 1) * Real.log r := Real.log_rpow hr_pos (τ + 1)
    have h7 : Real.log (Real.rpow r (τ + 1)) = (τ + 1) * Real.log r := by simpa using h71
    rw [h7]
    have h8 : Real.log (2000 * C) + Real.log 2 = Real.log (4000 * C) := by
      have h9 : Real.log (2000 * C) + Real.log 2 = Real.log ((2000 * C) * 2) := by
        rw [← Real.log_mul (by positivity) (by norm_num)] <;> ring
      rw [h9]
      have h10 : (2000 * C) * 2 = 4000 * C := by ring
      rw [h10]
    have h11 : Real.log (1 / r) = - Real.log r := by
      rw [Real.log_div (by norm_num) hr_pos.ne'] <;> simp
    have h_final : Real.log (2000 * C) - ((τ + 1) * Real.log r - Real.log 2) =
        Real.log (4000 * C) + (τ + 1) * Real.log (1 / r) := by
      calc Real.log (2000 * C) - ((τ + 1) * Real.log r - Real.log 2)
        = Real.log (2000 * C) + Real.log 2 - (τ + 1) * Real.log r := by ring
      _ = Real.log (4000 * C) - (τ + 1) * Real.log r := by rw [h8]
      _ = Real.log (4000 * C) + (τ + 1) * Real.log (1 / r) := by rw [h11] <;> ring
    exact h_final

  set A : ℝ := Real.log (4000 * C) + 1 with hA_def
  have hA_pos : 0 < A := by linarith [h_log4000C_pos]
  set B : ℝ := (τ + 1) / a with hB_def
  have hB_pos : 0 < B := by positivity
  set K1 : ℝ := 200 * C * (D_X : ℝ) * A with hK1_def
  set K2 : ℝ := 200 * C * (D_X : ℝ) * B with hK2_def
  have hK1_pos : 0 < K1 := by
    simp [hK1_def] <;> positivity
  have hK2_pos : 0 < K2 := by
    simp [hK2_def] <;> positivity
  set p1 : ℝ := εF - τ with hp1_def
  set p2 : ℝ := εF - τ - a with hp2_def
  have hp1_pos : 0 < p1 := by linarith
  have hp2_pos : 0 < p2 := by linarith [ha_def]

  -- L ≤ A + B * r^(-a) for 0 < r < 1
  have hL_bound : ∀ (r : ℝ), 0 < r → r < 1 →
      (max 0 (Real.log (2000 * C / ((Real.rpow r τ / 2) * r))) + 1) ≤
        A + B * Real.rpow r (-a) := by
    intro r hr_pos hr_lt_one
    set y : ℝ := Real.log (2000 * C / ((Real.rpow r τ / 2) * r)) with hy_def
    have hy_eq : y = Real.log (4000 * C) + (τ + 1) * Real.log (1 / r) := h_log_expr r hr_pos
    have h_log1 : Real.log (1 / r) ≤ Real.rpow r (-a) / a := h_log_bound r hr_pos hr_lt_one
    by_cases hy_nonneg : 0 ≤ y
    · have h_max : max 0 y = y := by rw [max_eq_right] <;> linarith
      rw [h_max, hy_eq]
      have h : (τ + 1) * Real.log (1 / r) ≤ (τ + 1) * (Real.rpow r (-a) / a) := by gcongr
      have hB_expr : B * Real.rpow r (-a) = (τ + 1) * (Real.rpow r (-a) / a) := by
        simp [hB_def] <;> ring
      linarith [hA_def]
    · have h_max : max 0 y = 0 := by rw [max_eq_left] <;> linarith
      rw [h_max]
      have h_rpow_pos : 0 < Real.rpow r (-a) := Real.rpow_pos_of_pos hr_pos (-a)
      have h9 : 0 < B * Real.rpow r (-a) := by positivity
      have h10 : (1 : ℝ) ≤ A := by linarith [hA_def, h_log4000C_pos]
      linarith

  set target : ℝ := Real.rpow 2 (-εF) with htarget_def
  have htarget_pos : 0 < target := Real.rpow_pos_of_pos (by norm_num) (-εF)
  have h_half_target_pos : 0 < target / 2 := by positivity

  rcases exists_rpow_small K1 (target / 2) hK1_pos h_half_target_pos hp1_pos with
    ⟨r1, hr1_pos, hr1_eq, h1_small⟩
  rcases exists_rpow_small K2 (target / 2) hK2_pos h_half_target_pos hp2_pos with
    ⟨r2, hr2_pos, hr2_eq, h2_small⟩

  let r₀ := min r1 (min r2 1)
  have hr₀_pos : 0 < r₀ := by positivity
  have hr₀_le_r1 : r₀ ≤ r1 := min_le_left _ _
  have hr₀_le_r2 : r₀ ≤ r2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hr₀_le_one : r₀ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)

  have hr₀_eq : r₀ = c_x_r_ext τ εF C D_X := by
    dsimp only [r₀, c_x_r_ext]
    rw [hr1_eq, hr2_eq]
    <;> rfl

  refine ⟨r₀, hr₀_pos, hr₀_eq, fun r hr_pos hr_lt => ?_⟩
  have hr_lt_r1 : r < r1 := lt_of_lt_of_le hr_lt hr₀_le_r1
  have hr_lt_r2 : r < r2 := lt_of_lt_of_le hr_lt hr₀_le_r2
  have hr_lt_one : r < 1 := lt_of_lt_of_le hr_lt hr₀_le_one

  let m := Real.rpow r τ / 2
  let L := max 0 (Real.log (2000 * C / (m * r))) + 1
  let C_X := 100 * C * L / m

  have h_m_pos : 0 < Real.rpow r τ := Real.rpow_pos_of_pos hr_pos τ
  have hm_pos : 0 < m := by
    dsimp only [m]
    exact div_pos h_m_pos (by norm_num)

  have hL_bound' : L ≤ A + B * Real.rpow r (-a) := hL_bound r hr_pos hr_lt_one

  have h_m_inv : 1 / m = 2 * Real.rpow r (-τ) := by
    dsimp only [m]
    have h1 : 1 / (Real.rpow r τ / 2) = 2 / Real.rpow r τ := by
      field_simp [h_m_pos.ne'] <;> ring
    rw [h1]
    have h2 : 2 / Real.rpow r τ = 2 * Real.rpow r (-τ) := by
      have h3 : Real.rpow r (-τ) = (Real.rpow r τ)⁻¹ := Real.rpow_neg hr_pos.le τ
      rw [h3] <;> ring
    exact h2

  have h5 : Real.rpow r (-τ) * Real.rpow r (-a) = Real.rpow r (-τ - a) := by
    have h6 : Real.rpow r ((-τ) + (-a)) = Real.rpow r (-τ) * Real.rpow r (-a) :=
      Real.rpow_add hr_pos (-τ) (-a)
    have h7 : (-τ) + (-a) = -τ - a := by ring
    rw [h7] at h6
    exact h6.symm

  have h12 : Real.rpow r (p1 - εF) = Real.rpow r p1 * Real.rpow r (-εF) := by
    have h13 : Real.rpow r (p1 + (-εF)) = Real.rpow r p1 * Real.rpow r (-εF) :=
      Real.rpow_add hr_pos p1 (-εF)
    have h14 : p1 - εF = p1 + (-εF) := by ring
    rw [h14]
    exact h13
  have h13 : Real.rpow r (p2 - εF) = Real.rpow r p2 * Real.rpow r (-εF) := by
    have h14 : Real.rpow r (p2 + (-εF)) = Real.rpow r p2 * Real.rpow r (-εF) :=
      Real.rpow_add hr_pos p2 (-εF)
    have h15 : p2 - εF = p2 + (-εF) := by ring
    rw [h15]
    exact h14

  have hC_X_bound : C_X * (D_X : ℝ) ≤
      (K1 * Real.rpow r p1 + K2 * Real.rpow r p2) * Real.rpow r (-εF) := by
    dsimp only [C_X]
    have h_eq1 : C_X * (D_X : ℝ) = 200 * C * (D_X : ℝ) * Real.rpow r (-τ) * L := by
      have h21 : C_X * (D_X : ℝ) = 100 * C * L * (D_X : ℝ) / m := by ring
      rw [h21]
      have h22 : 100 * C * L * (D_X : ℝ) / m =
          100 * C * L * (D_X : ℝ) * (1 / m) := by ring
      rw [h22, h_m_inv] <;> ring
    rw [h_eq1]
    have h_rpow_negτ_pos : 0 < Real.rpow r (-τ) := Real.rpow_pos_of_pos hr_pos (-τ)
    have h_pos_coeff : 0 ≤ 200 * C * (D_X : ℝ) * Real.rpow r (-τ) := by
      have h1 : 0 ≤ C := by linarith
      have h2 : 0 ≤ (D_X : ℝ) := by positivity
      have h3 : 0 ≤ Real.rpow r (-τ) := h_rpow_negτ_pos.le
      positivity
    have h_step1 : 200 * C * (D_X : ℝ) * Real.rpow r (-τ) * L ≤
        200 * C * (D_X : ℝ) * Real.rpow r (-τ) * (A + B * Real.rpow r (-a)) :=
      mul_le_mul_of_nonneg_left hL_bound' h_pos_coeff
    have h_step2 : 200 * C * (D_X : ℝ) * Real.rpow r (-τ) * (A + B * Real.rpow r (-a)) =
        200 * C * (D_X : ℝ) * A * Real.rpow r (-τ) +
        200 * C * (D_X : ℝ) * B * Real.rpow r (-τ - a) := by
      have h_expand : 200 * C * (D_X : ℝ) * Real.rpow r (-τ) * (A + B * Real.rpow r (-a)) =
          200 * C * (D_X : ℝ) * A * Real.rpow r (-τ) +
          200 * C * (D_X : ℝ) * B * (Real.rpow r (-τ) * Real.rpow r (-a)) := by ring
      rw [h_expand, h5] <;> ring
    have h8 : -τ = p1 - εF := by linarith [hp1_def]
    have h9 : -τ - a = p2 - εF := by linarith [hp2_def]
    have h_step3 : 200 * C * (D_X : ℝ) * A * Real.rpow r (-τ) +
                     200 * C * (D_X : ℝ) * B * Real.rpow r (-τ - a) =
        200 * C * (D_X : ℝ) * A * Real.rpow r (p1 - εF) +
        200 * C * (D_X : ℝ) * B * Real.rpow r (p2 - εF) := by
      have h10 : Real.rpow r (-τ) = Real.rpow r (p1 - εF) := by rw [show -τ = p1 - εF by linarith [hp1_def]]
      have h11 : Real.rpow r (-τ - a) = Real.rpow r (p2 - εF) := by rw [show -τ - a = p2 - εF by linarith [hp2_def]]
      rw [h10, h11]
    have h_step4 : 200 * C * (D_X : ℝ) * A * Real.rpow r (p1 - εF) +
                     200 * C * (D_X : ℝ) * B * Real.rpow r (p2 - εF) =
        (K1 * Real.rpow r p1 + K2 * Real.rpow r p2) * Real.rpow r (-εF) := by
      rw [h12, h13]
      simp [hK1_def, hK2_def] <;> ring
    calc 200 * C * (D_X : ℝ) * Real.rpow r (-τ) * L
      ≤ 200 * C * (D_X : ℝ) * Real.rpow r (-τ) * (A + B * Real.rpow r (-a)) := h_step1
    _ = 200 * C * (D_X : ℝ) * A * Real.rpow r (-τ) +
        200 * C * (D_X : ℝ) * B * Real.rpow r (-τ - a) := h_step2
    _ = 200 * C * (D_X : ℝ) * A * Real.rpow r (p1 - εF) +
        200 * C * (D_X : ℝ) * B * Real.rpow r (p2 - εF) := h_step3
    _ = (K1 * Real.rpow r p1 + K2 * Real.rpow r p2) * Real.rpow r (-εF) := h_step4

  have h1_small' : K1 * Real.rpow r p1 ≤ target / 2 := h1_small r hr_pos hr_lt_r1
  have h2_small' : K2 * Real.rpow r p2 ≤ target / 2 := h2_small r hr_pos hr_lt_r2
  have h_sum : K1 * Real.rpow r p1 + K2 * Real.rpow r p2 ≤ target := by linarith

  have h_rpow2 : Real.rpow (2 * r) (-εF) = target * Real.rpow r (-εF) := by
    have h : Real.rpow (2 * r) (-εF) = Real.rpow 2 (-εF) * Real.rpow r (-εF) :=
      Real.mul_rpow (by norm_num) (by linarith)
    exact h

  have h_rpow_negεF_pos : 0 < Real.rpow r (-εF) := Real.rpow_pos_of_pos hr_pos (-εF)
  calc C_X * (D_X : ℝ)
    ≤ (K1 * Real.rpow r p1 + K2 * Real.rpow r p2) * Real.rpow r (-εF) := hC_X_bound
    _ ≤ target * Real.rpow r (-εF) :=
      mul_le_mul_of_nonneg_right h_sum h_rpow_negεF_pos.le
    _ = Real.rpow (2 * r) (-εF) := h_rpow2.symm

end RadialBootstrapping
