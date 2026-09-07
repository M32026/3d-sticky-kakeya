module

public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# C_B exponent bound lemma

Standalone lemma proving that for sufficiently small r,
`60000 * K^2 * 34^σ * D_T^7 * r^(ε_F - κ - 5τ) ≤ 2^(-ε_F)`.

This establishes `C_B * D_T ≤ (2*r)^(-ε_F)` in the multi-tube
Step B wrapper, where `C_B = 60000 * K^2 * 34^σ * D_T^6 * r^(-(κ+5*τ))`.
-/

namespace RadialBootstrapping
namespace CBBound

/-- Generic lemma: Given `α > 0`, `C > 0`, `B > 0`, and
`0 < r ≤ (C / B)^(-1/α)`, prove `C * r^α ≤ B`. -/
lemma generic_small_rpow_bound {C r α B : ℝ}
    (hC_pos : 0 < C) (hr_pos : 0 < r) (hα_pos : 0 < α) (hB_pos : 0 < B)
    (h : r ≤ Real.rpow (C / B) (-1 / α)) :
    C * Real.rpow r α ≤ B := by
  have h1 : Real.rpow r α ≤ Real.rpow (Real.rpow (C / B) (-1 / α)) α :=
    Real.rpow_le_rpow hr_pos.le h hα_pos.le
  have hCB_pos : 0 < C / B := div_pos hC_pos hB_pos
  have h2 : Real.rpow (Real.rpow (C / B) (-1 / α)) α =
      Real.rpow (C / B) ((-1 / α) * α) :=
    (Real.rpow_mul hCB_pos.le (-1 / α) α).symm
  have h3 : (-1 / α) * α = -1 := by
    field_simp [hα_pos.ne'] <;> ring
  rw [h2, h3] at h1
  have h4 : Real.rpow (C / B) (-1 : ℝ) = (C / B)⁻¹ := by
    simpa [Real.rpow_neg_one] using rfl
  rw [h4] at h1
  have h5 : (C / B)⁻¹ = B / C := by
    field_simp [hC_pos.ne', hB_pos.ne'] <;> ring
  rw [h5] at h1
  have h6 : C * Real.rpow r α ≤ C * (B / C) :=
    mul_le_mul_of_nonneg_left h1 hC_pos.le
  have h7 : C * (B / C) = B := by
    field_simp [hC_pos.ne'] <;> ring
  rw [h7] at h6
  exact h6

/-- Derive `0 < ε_F - κ - 5*τ` from `8*τ + 3*κ < ε_F`, `0 < κ`, `0 < τ`. -/
lemma exponent_pos {ε_F κ τ : ℝ} (hεF_large : 8 * τ + 3 * κ < ε_F)
    (hκ_pos : 0 < κ) (hτ_pos : 0 < τ) :
    0 < ε_F - κ - 5 * τ := by
  have h1 : ε_F - κ - 5 * τ > 8 * τ + 3 * κ - κ - 5 * τ := by linarith
  have h2 : 8 * τ + 3 * κ - κ - 5 * τ = 3 * τ + 2 * κ := by ring
  rw [h2] at h1
  linarith

/-- The constant `60000 * K^2 * 34^σ * D_T^7` is positive. -/
lemma cb_const_pos {K D_T σ : ℝ} (hK : 1 ≤ K) (hDT : 1 ≤ D_T) (hσ : 0 ≤ σ) :
    0 < 60000 * K^2 * (34 : ℝ)^σ * D_T^7 := by
  have h1 : 0 < K := by linarith
  have h2 : 0 < D_T := by linarith
  have h3 : 0 < (34 : ℝ)^σ := Real.rpow_pos_of_pos (by norm_num) σ
  positivity

/-- **C_B exponent bound**: If r is sufficiently small, then
`60000 * K^2 * 34^σ * D_T^7 * r^(ε_F - κ - 5τ) ≤ 2^(-ε_F)`.

This is exactly what is needed for `C_B * D_T ≤ (2*r)^(-ε_F)`.

The sufficient condition is
`r ≤ ((60000 * K^2 * 34^σ * D_T^7) / 2^(-ε_F))^(-1/(ε_F - κ - 5τ))`
which simplifies to
`r ≤ (60000 * K^2 * 34^σ * D_T^7 * 2^ε_F)^(-1/(ε_F - κ - 5τ))`.
-/
lemma cB_times_DT_bound {K D_T r σ ε_F κ τ : ℝ}
    (hK : 1 ≤ K) (hDT : 1 ≤ D_T) (hσ : 0 ≤ σ) (hσ_lt_one : σ < 1)
    (hεF_large : 8 * τ + 3 * κ < ε_F)
    (hκ_pos : 0 < κ) (hτ_pos : 0 < τ) (hεF_pos : 0 < ε_F)
    (hr_pos : 0 < r)
    (hr_sufficiently_small :
      r ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * D_T^7 / Real.rpow (2 : ℝ) (-ε_F))
        (-1 / (ε_F - κ - 5 * τ))) :
    60000 * K^2 * (34 : ℝ)^σ * D_T^7 * Real.rpow r (ε_F - κ - 5 * τ) ≤
      Real.rpow (2 : ℝ) (-ε_F) := by
  set α : ℝ := ε_F - κ - 5 * τ with hα_def
  set C : ℝ := 60000 * K^2 * (34 : ℝ)^σ * D_T^7 with hC_def
  set B : ℝ := Real.rpow (2 : ℝ) (-ε_F) with hB_def
  have hα_pos : 0 < α := exponent_pos hεF_large hκ_pos hτ_pos
  have hC_pos : 0 < C := cb_const_pos hK hDT hσ
  have hB_pos : 0 < B := Real.rpow_pos_of_pos (by norm_num) (-ε_F)
  exact generic_small_rpow_bound hC_pos hr_pos hα_pos hB_pos hr_sufficiently_small

/-- Complete proof of the C_B bound from the hC_B_r0 smallness hypothesis.
    Two-case split on max(C_B_raw, 1). -/
lemma C_B_bound_from_r0
    {K σ ε_F κ τ r_sel r0 : ℝ} {D_T : ℕ}
    (hK : 1 ≤ K) (hσ_pos : 0 < σ)
    (hεF_pos : 0 < ε_F) (hεF_large3 : 8 * τ + 3 * κ < ε_F)
    (hκ_pos : 0 < κ) (hτ : 0 < τ)
    (hr_sel_pos : 0 < r_sel) (hr_sel_le : r_sel ≤ r0) (hr_sel_small : r_sel < 1)
    (hD_T_pos : 0 < D_T)
    (hC_B_r0 : ∀ (r : ℝ), 0 < r → r ≤ r0 →
      r ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
        (-1 / (ε_F - κ - 5 * τ))) :
    (max (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
      Real.rpow r_sel (-(κ + 5 * τ))) 1) * (D_T : ℝ) ≤
    Real.rpow (2 * r_sel) (-ε_F) := by
  set p : ℝ := ε_F - κ - 5 * τ with hp_def
  have hp_pos : 0 < p := by linarith
  have hDT_ge_one : (1 : ℝ) ≤ (D_T : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hD_T_pos)
  have h34σ_ge_one : (1 : ℝ) ≤ (34 : ℝ)^σ := by
    have h1 : (1 : ℝ) ≤ (34 : ℝ) := by norm_num
    have h2 : 0 ≤ σ := by linarith
    exact Real.one_le_rpow h1 h2
  set two_neg_εF : ℝ := Real.rpow (2 : ℝ) (-ε_F) with htwo_def
  have htwo_pos : 0 < two_neg_εF := Real.rpow_pos_of_pos (by norm_num) _
  set big_const : ℝ := 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 with hbig_def
  have hbig_pos : 0 < big_const := by positivity
  set A : ℝ := big_const / two_neg_εF with hA_def
  have hA_pos : 0 < A := div_pos hbig_pos htwo_pos
  have h1 : r_sel ≤ Real.rpow A (-1 / p) := hC_B_r0 r_sel hr_sel_pos hr_sel_le
  have h_rpow_pow : Real.rpow (Real.rpow A (-1 / p)) p = Real.rpow A (-1 : ℝ) := by
    have h : Real.rpow A ((-1 / p) * p) = Real.rpow (Real.rpow A (-1 / p)) p :=
      Real.rpow_mul hA_pos.le (-1 / p) p
    rw [←h]
    have h2 : (-1 / p) * p = -1 := by field_simp [hp_pos.ne'] <;> ring
    rw [h2]
  have h2 : Real.rpow r_sel p ≤ Real.rpow A (-1 : ℝ) := by
    have h4 : Real.rpow r_sel p ≤ Real.rpow (Real.rpow A (-1 / p)) p :=
      Real.rpow_le_rpow hr_sel_pos.le h1 hp_pos.le
    rw [h_rpow_pow] at h4
    exact h4
  have h_r_sel_p_le : Real.rpow r_sel p ≤ 1 / A := by
    have h5 : Real.rpow A (-1 : ℝ) = 1 / A := by
      simpa using Real.rpow_neg hA_pos.le 1
    rw [h5] at h2
    exact h2
  have h_key : big_const * Real.rpow r_sel p ≤ two_neg_εF := by
    have h6 : Real.rpow r_sel p ≤ 1 / A := h_r_sel_p_le
    have h7 : 1 / A = two_neg_εF / big_const := by
      dsimp only [A]
      field_simp [hbig_pos.ne', htwo_pos.ne'] <;> ring
    rw [h7] at h6
    have h8 : big_const * Real.rpow r_sel p ≤ big_const * (two_neg_εF / big_const) := by gcongr
    have h9 : big_const * (two_neg_εF / big_const) = two_neg_εF := by
      field_simp [hbig_pos.ne'] <;> ring
    rw [h9] at h8
    exact h8
  have hRHS : Real.rpow (2 * r_sel) (-ε_F) = two_neg_εF * Real.rpow r_sel (-ε_F) := by
    have h : Real.rpow (2 * r_sel) (-ε_F) = Real.rpow (2 : ℝ) (-ε_F) * Real.rpow r_sel (-ε_F) :=
      Real.mul_rpow (by norm_num) hr_sel_pos.le
    exact h
  have h_neg_exp_eq : -(κ + 5 * τ) = -ε_F + p := by
    simp only [hp_def] <;> ring
  have h_r_sel_neg_εF_gt : Real.rpow r_sel (-ε_F) > Real.rpow r_sel (-p) := by
    have h1 : r_sel < 1 := hr_sel_small
    have h2 : -ε_F < -p := by linarith
    exact Real.rpow_lt_rpow_of_exponent_gt hr_sel_pos h1 h2
  by_cases h_case : 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
      Real.rpow r_sel (-(κ + 5 * τ)) ≥ 1
  · -- Case 1
    have h_max : max (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
        Real.rpow r_sel (-(κ + 5 * τ))) 1 =
        60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
        Real.rpow r_sel (-(κ + 5 * τ)) := by
      rw [max_eq_left h_case]
    rw [h_max, hRHS]
    have h13 : Real.rpow r_sel (-(κ + 5 * τ)) =
        Real.rpow r_sel (-ε_F) * Real.rpow r_sel p := by
      rw [h_neg_exp_eq]
      exact Real.rpow_add hr_sel_pos (-ε_F) p
    rw [h13]
    have h14 : (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
        (Real.rpow r_sel (-ε_F) * Real.rpow r_sel p)) * (D_T : ℝ) =
        Real.rpow r_sel (-ε_F) * (big_const * Real.rpow r_sel p) := by
      simp only [hbig_def] <;> ring
    rw [h14]
    have h15 : big_const * Real.rpow r_sel p ≤ two_neg_εF := h_key
    have h16 : 0 ≤ Real.rpow r_sel (-ε_F) := Real.rpow_nonneg hr_sel_pos.le _
    nlinarith
  · -- Case 2
    have h_case' : 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
        Real.rpow r_sel (-(κ + 5 * τ)) < 1 := by linarith
    have h_max : max (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^6 *
        Real.rpow r_sel (-(κ + 5 * τ))) 1 = 1 := by
      rw [max_eq_right] <;> linarith
    rw [h_max, hRHS]
    have h24 : two_neg_εF * Real.rpow r_sel (-ε_F) >
        two_neg_εF * Real.rpow r_sel (-p) := by
      exact mul_lt_mul_of_pos_left h_r_sel_neg_εF_gt htwo_pos
    have h25 : two_neg_εF * Real.rpow r_sel (-p) ≥ big_const := by
      have h_rp_pos : 0 < Real.rpow r_sel p := Real.rpow_pos_of_pos hr_sel_pos p
      have h26 : Real.rpow r_sel (-p) ≥ A := by
        have h27 : Real.rpow r_sel (-p) = (Real.rpow r_sel p)⁻¹ :=
          Real.rpow_neg hr_sel_pos.le p
        rw [h27]
        have h28 : (Real.rpow r_sel p)⁻¹ ≥ (1 / A)⁻¹ := by
          gcongr
          <;> linarith [h_r_sel_p_le]
        have h29 : (1 / A)⁻¹ = A := by
          field_simp [hA_pos.ne']
        rw [h29] at h28
        exact h28
      have h30 : two_neg_εF * Real.rpow r_sel (-p) ≥ two_neg_εF * A := by gcongr
      have h31 : two_neg_εF * A = big_const := by
        dsimp only [A]
        field_simp [htwo_pos.ne'] <;> ring
      rw [h31] at h30
      exact h30
    have h32 : big_const ≥ (D_T : ℝ)^7 := by
      have h33 : 60000 * K^2 * (34 : ℝ)^σ ≥ 1 := by
        have h34 : (60000 : ℝ) ≥ 1 := by norm_num
        nlinarith [h34σ_ge_one]
      simp only [hbig_def]
      nlinarith
    have h35 : (D_T : ℝ)^7 ≥ (D_T : ℝ) := by
      have h36 : (1 : ℝ) ≤ (D_T : ℝ) := hDT_ge_one
      have h37 : (D_T : ℝ)^7 ≥ (D_T : ℝ)^1 := by
        gcongr <;> norm_num
      simpa using h37
    nlinarith

/-- The C_B smallness threshold is positive. -/
lemma cB_threshold_pos {K σ ε_F κ τ : ℝ} {D_T : ℕ}
    (hK : 1 ≤ K) (hσ : 0 ≤ σ) (hεF_pos : 0 < ε_F)
    (hεF_large : 8 * τ + 3 * κ < ε_F)
    (hκ_pos : 0 < κ) (hτ_pos : 0 < τ) (hD_T_pos : 0 < D_T) :
    0 < Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
        (-1 / (ε_F - κ - 5 * τ)) := by
  set α : ℝ := ε_F - κ - 5 * τ with hα_def
  have hα_pos : 0 < α := exponent_pos hεF_large hκ_pos hτ_pos
  set C : ℝ := 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 with hC_def
  set B : ℝ := Real.rpow (2 : ℝ) (-ε_F) with hB_def
  have hC_pos : 0 < C := cb_const_pos hK (by exact_mod_cast hD_T_pos) hσ
  have hB_pos : 0 < B := Real.rpow_pos_of_pos (by norm_num) (-ε_F)
  have hA_pos : 0 < C / B := div_pos hC_pos hB_pos
  exact Real.rpow_pos_of_pos hA_pos (-1 / α)

/-- Establish `hC_B_r0` from `r0 ≤ threshold`.

If `r0` is below the C_B smallness threshold, then every `0 < r ≤ r0`
is also below the threshold, which is exactly the `hC_B_r0` condition
required by `bootstrapping_one_direction_G`. -/
lemma hC_B_r0_of_le_threshold {K σ ε_F κ τ r0 : ℝ} {D_T : ℕ}
    (hK : 1 ≤ K) (hσ : 0 ≤ σ) (hεF_pos : 0 < ε_F)
    (hεF_large : 8 * τ + 3 * κ < ε_F)
    (hκ_pos : 0 < κ) (hτ_pos : 0 < τ) (hD_T_pos : 0 < D_T)
    (hr0_le_threshold : r0 ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
        (-1 / (ε_F - κ - 5 * τ))) :
    ∀ (r : ℝ), 0 < r → r ≤ r0 →
      r ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
        (-1 / (ε_F - κ - 5 * τ)) := by
  intro r _ hr_le
  exact le_trans hr_le hr0_le_threshold

/-- Equivalence: `r ≤ threshold` iff the C_B bound holds.

This shows the threshold is exactly the right one:
`r ≤ T` ⇔ `60000 * K^2 * 34^σ * D_T^7 * r^(ε_F - κ - 5τ) ≤ 2^(-ε_F)`. -/
lemma cB_threshold_iff {K σ ε_F κ τ r : ℝ} {D_T : ℕ}
    (hK : 1 ≤ K) (hσ : 0 ≤ σ) (hεF_pos : 0 < ε_F)
    (hεF_large : 8 * τ + 3 * κ < ε_F)
    (hκ_pos : 0 < κ) (hτ_pos : 0 < τ) (hD_T_pos : 0 < D_T)
    (hr_pos : 0 < r) :
    r ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
        (-1 / (ε_F - κ - 5 * τ)) ↔
      60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 * Real.rpow r (ε_F - κ - 5 * τ) ≤
        Real.rpow (2 : ℝ) (-ε_F) := by
  set α : ℝ := ε_F - κ - 5 * τ with hα_def
  have hα_pos : 0 < α := exponent_pos hεF_large hκ_pos hτ_pos
  set C : ℝ := 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 with hC_def
  set B : ℝ := Real.rpow (2 : ℝ) (-ε_F) with hB_def
  have hC_pos : 0 < C := cb_const_pos hK (by exact_mod_cast hD_T_pos) hσ
  have hB_pos : 0 < B := Real.rpow_pos_of_pos (by norm_num) (-ε_F)
  set A : ℝ := C / B with hA_def
  have hA_pos : 0 < A := div_pos hC_pos hB_pos
  set T : ℝ := Real.rpow A (-1 / α) with hT_def
  have hT_pos : 0 < T := Real.rpow_pos_of_pos hA_pos (-1 / α)
  have h1 : Real.rpow T α = 1 / A := by
    have h2 : Real.rpow T α = Real.rpow (Real.rpow A (-1 / α)) α := by rw [hT_def]
    rw [h2]
    have h3 : Real.rpow (Real.rpow A (-1 / α)) α = Real.rpow A ((-1 / α) * α) :=
      (Real.rpow_mul hA_pos.le (-1 / α) α).symm
    rw [h3]
    have h4 : (-1 / α) * α = -1 := by field_simp [hα_pos.ne'] <;> ring
    rw [h4]
    have h5 : Real.rpow A (-1 : ℝ) = 1 / A := by
      simpa using Real.rpow_neg hA_pos.le 1
    rw [h5]
  constructor
  · -- Forward direction: r ≤ T → C * r^α ≤ B
    intro h_le
    have h5 : Real.rpow r α ≤ Real.rpow T α := Real.rpow_le_rpow hr_pos.le h_le hα_pos.le
    rw [h1] at h5
    have h6 : C * Real.rpow r α ≤ C * (1 / A) := mul_le_mul_of_nonneg_left h5 hC_pos.le
    have h7 : C * (1 / A) = B := by
      dsimp only [A]
      field_simp [hC_pos.ne', hB_pos.ne']
    rw [h7] at h6
    exact h6
  · -- Backward direction: C * r^α ≤ B → r ≤ T
    intro h_bound
    have h5 : Real.rpow r α ≤ 1 / A := by
      have h6 : C * Real.rpow r α ≤ B := h_bound
      have h7 : Real.rpow r α ≤ B / C := by
        calc Real.rpow r α
          = (C * Real.rpow r α) / C := by field_simp [hC_pos.ne']
        _ ≤ B / C := by gcongr
      have h8 : B / C = 1 / A := by
        dsimp only [A]
        field_simp [hC_pos.ne', hB_pos.ne']
      rw [h8] at h7
      exact h7
    have h9 : Real.rpow r α ≤ Real.rpow T α := by rw [h1] <;> exact h5
    have h10 : r ≤ T := by
      by_contra h
      have h11 : T < r := by linarith
      have h12 : Real.rpow T α < Real.rpow r α := Real.rpow_lt_rpow (by linarith) h11 hα_pos
      linarith
    exact h10

end CBBound
end RadialBootstrapping
