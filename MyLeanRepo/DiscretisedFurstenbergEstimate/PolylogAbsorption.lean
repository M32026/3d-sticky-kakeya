module

/-
  PolylogAbsorption.lean

  General lemma: any polylog factor (log(2/Δ))^A is dominated by Δ^{-ε}
  for sufficiently small Δ. Used to absorb thick-tube-cover polylog constants
  (K, C₂) into polynomial C_abs = Δ^{-η/2}.

  Key Mathlib fact: `isLittleO_rpow_exp_pos_mul_atTop`.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace PolylogAbsorption

-- Helper: x^(-y) = (x^y)⁻¹ for x > 0
lemma rpow_neg' {x y : ℝ} (hx : 0 < x) : Real.rpow x (-y) = (Real.rpow x y)⁻¹ := by
  have h : (x ^ (-y)) = (x ^ y)⁻¹ := Real.rpow_neg hx.le y
  exact h

-- Helper: (exp y)^z = exp (y * z)
lemma exp_rpow_real (y z : ℝ) : Real.rpow (Real.exp y) z = Real.exp (y * z) := by
  have h_pos : 0 < Real.exp y := Real.exp_pos y
  have h_pos2 : 0 < Real.rpow (Real.exp y) z := Real.rpow_pos_of_pos h_pos _
  have h_log : Real.log (Real.rpow (Real.exp y) z) = z * y := by
    have h' : Real.log ((Real.exp y) ^ z) = z * Real.log (Real.exp y) :=
      Real.log_rpow h_pos z
    have h_eq : (Real.exp y) ^ z = Real.rpow (Real.exp y) z := by rfl
    rw [h_eq] at h'
    have h'' : Real.log (Real.exp y) = y := Real.log_exp y
    rw [h', h''] <;> ring
  have h_eq : Real.rpow (Real.exp y) z = Real.exp (Real.log (Real.rpow (Real.exp y) z)) :=
    (Real.exp_log h_pos2).symm
  rw [h_eq, h_log]
  congr 1 <;> ring

-- Helper: (a * b)^c = a^c * b^c for a, b > 0
lemma mul_rpow_real {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.rpow (a * b) c = Real.rpow a c * Real.rpow b c := by
  have h_pos1 : 0 < a * b := mul_pos ha hb
  have h_p2 : 0 < Real.rpow a c := Real.rpow_pos_of_pos ha _
  have h_p3 : 0 < Real.rpow b c := Real.rpow_pos_of_pos hb _
  have h_l1 : Real.log (Real.rpow (a * b) c) = c * Real.log (a * b) := by
    have h' : Real.log ((a * b) ^ c) = c * Real.log (a * b) := Real.log_rpow h_pos1 c
    have h_eq : (a * b) ^ c = Real.rpow (a * b) c := by rfl
    rw [h_eq] at h'; exact h'
  have h_l2 : Real.log (Real.rpow a c * Real.rpow b c) = c * Real.log (a * b) := by
    rw [Real.log_mul h_p2.ne' h_p3.ne']
    have h1 : Real.log (Real.rpow a c) = c * Real.log a := by
      have h' : Real.log (a ^ c) = c * Real.log a := Real.log_rpow ha c
      have h_eq : a ^ c = Real.rpow a c := by rfl
      rw [h_eq] at h'; exact h'
    have h2 : Real.log (Real.rpow b c) = c * Real.log b := by
      have h' : Real.log (b ^ c) = c * Real.log b := Real.log_rpow hb c
      have h_eq : b ^ c = Real.rpow b c := by rfl
      rw [h_eq] at h'; exact h'
    rw [h1, h2, Real.log_mul ha.ne' hb.ne'] <;> ring
  have h_p4 : 0 < Real.rpow (a * b) c := Real.rpow_pos_of_pos h_pos1 _
  have h_p5 : 0 < Real.rpow a c * Real.rpow b c := mul_pos h_p2 h_p3
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_p4) (Set.mem_Ioi.mpr h_p5) (by rw [h_l1, h_l2])

-- Helper: x^y * x^z = x^(y+z) for x > 0
lemma rpow_add' {x y z : ℝ} (hx : 0 < x) :
    Real.rpow x y * Real.rpow x z = Real.rpow x (y + z) := by
  have h : x ^ (y + z) = (x ^ y) * (x ^ z) := Real.rpow_add hx y z
  have h' : (x ^ y) * (x ^ z) = x ^ (y + z) := h.symm
  have h1 : (x ^ y) * (x ^ z) = Real.rpow x y * Real.rpow x z := by rfl
  have h2 : x ^ (y + z) = Real.rpow x (y + z) := by rfl
  rw [h1, h2] at h'
  exact h'

/-- For A > 0, ε > 0, ∃ Δ₀ ∈ (0,1] such that ∀ 0 < Δ ≤ Δ₀:
  (log(2/Δ))^A ≤ Δ^{-ε}. -/
lemma polylog_absorption_real {A ε : ℝ} (hA_pos : 0 < A) (hε_pos : 0 < ε) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ Δ₀ ≤ 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ Δ₀ →
        Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε) := by
  have h_olo : (fun x : ℝ => Real.rpow x A) =o[Filter.atTop] (fun x : ℝ => Real.exp (ε * x)) :=
    isLittleO_rpow_exp_pos_mul_atTop A (b := ε) hε_pos
  let c : ℝ := Real.rpow 2 (-ε)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : ∀ (d : ℝ), 0 < d → ∃ (a : ℝ), ∀ (b : ℝ), a ≤ b →
      |Real.rpow b A| ≤ d * Real.exp (ε * b) := by
    simpa [Asymptotics.isLittleO_iff] using h_olo
  rcases h1 c hc_pos with ⟨X, hX⟩
  let X' : ℝ := max X 1
  have hX'_ge_X : X' ≥ X := le_max_left _ _
  have hX'_pos : 0 < X' := by have h : X' ≥ 1 := le_max_right _ _; linarith
  have hX' : ∀ (x : ℝ), x ≥ X' → Real.rpow x A ≤ c * Real.exp (ε * x) := by
    intro x hx
    have h2 : |Real.rpow x A| ≤ c * Real.exp (ε * x) := hX x (by linarith)
    have h3 : 0 < x := by linarith
    have h4 : 0 ≤ Real.rpow x A := Real.rpow_nonneg h3.le _
    have h5 : |Real.rpow x A| = Real.rpow x A := abs_of_nonneg h4
    rw [h5] at h2; exact h2
  let Δ₀ : ℝ := 2 * Real.exp (-X')
  have hΔ₀_pos : 0 < Δ₀ := by positivity
  have hΔ₀_le_one : Δ₀ ≤ 1 := by
    dsimp only [Δ₀]
    have h_exp : Real.exp (-X') ≤ 1 / 2 := by
      have h1 : -X' ≤ -1 := by linarith [le_max_right X 1]
      have h2 : Real.exp (-X') ≤ Real.exp (-1 : ℝ) := Real.exp_le_exp.mpr h1
      have h3 : Real.exp (-1 : ℝ) < 1 / 2 := by
        have h4 : Real.exp 1 > 2 := by
          linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
        have h5 : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by
          rw [Real.exp_neg] <;> ring
        rw [h5]
        gcongr
      linarith
    nlinarith
  have h_main : ∀ Δ : ℝ, 0 < Δ → Δ ≤ Δ₀ →
      Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε) := by
    intro Δ hΔ_pos hΔ_le
    have hΔ_lt_two : Δ < 2 := by
      have h1 : Δ ≤ Δ₀ := hΔ_le
      have h2 : Δ₀ ≤ 1 := hΔ₀_le_one
      linarith
    let x : ℝ := Real.log (2 / Δ)
    have hx_pos : 0 < x := by
      dsimp only [x]
      have h1 : (2 : ℝ) / Δ > 1 := by
        have h2 : Δ < 2 := hΔ_lt_two
        have h3 : (2 : ℝ) / Δ > (2 : ℝ) / 2 := by gcongr
        norm_num at h3 ⊢ <;> exact h3
      exact Real.log_pos h1
    have hx_ge : x ≥ X' := by
      dsimp only [x, Δ₀]
      have h1 : (2 : ℝ) / Δ ≥ (2 : ℝ) / Δ₀ := by gcongr
      have h2 : Real.log (2 / Δ) ≥ Real.log (2 / Δ₀) := Real.log_le_log (by positivity) h1
      have h3 : (2 : ℝ) / Δ₀ = Real.exp X' := by
        dsimp only [Δ₀]
        have h4 : (2 : ℝ) / (2 * Real.exp (-X')) = (Real.exp (-X'))⁻¹ := by field_simp
        rw [h4]
        have h5 : (Real.exp (-X'))⁻¹ = Real.exp X' := by
          rw [← Real.exp_neg] <;> ring_nf
        exact h5
      rw [h3] at h2
      have h4 : Real.log (Real.exp X') = X' := Real.log_exp X'
      rw [h4] at h2; exact h2
    have h5 : Real.rpow x A ≤ c * Real.exp (ε * x) := hX' x hx_ge
    have h71 : Δ = 2 * Real.exp (-x) := by
      dsimp only [x]
      have h9 : Real.exp (Real.log (2 / Δ)) = 2 / Δ := Real.exp_log (by positivity)
      have h10 : Real.exp (-x) = Δ / 2 := by
        rw [Real.exp_neg, h9] <;> field_simp [hΔ_pos.ne'] <;> ring
      linarith
    have h7 : Real.rpow Δ (-ε) = c * Real.exp (ε * x) := by
      rw [h71]
      have h12 : Real.rpow (2 * Real.exp (-x)) (-ε) =
          Real.rpow 2 (-ε) * Real.rpow (Real.exp (-x)) (-ε) :=
        mul_rpow_real (by norm_num) (Real.exp_pos _)
      rw [h12]
      have h13 : Real.rpow (Real.exp (-x)) (-ε) = Real.exp (ε * x) := by
        rw [exp_rpow_real (-x) (-ε)] <;> ring_nf
      rw [h13] <;> rfl
    rw [h7]; exact h5
  exact ⟨Δ₀, hΔ₀_pos, hΔ₀_le_one, h_main⟩

/-- Natural-number version. -/
lemma polylog_absorption_nat {n : ℕ} {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ Δ₀ ≤ 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ Δ₀ →
        (Real.log (2 / Δ)) ^ n ≤ Real.rpow Δ (-ε) := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨1, by norm_num, by norm_num, fun Δ hΔ_pos hΔ_le => ?_⟩
    have h1 : (Real.log (2 / Δ)) ^ 0 = 1 := by simp
    rw [h1]
    have h5 : Real.rpow Δ ε ≤ 1 := by
      have h6 : Real.rpow Δ ε ≤ Real.rpow 1 ε := Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      simpa using h6
    have h7 : 0 < Real.rpow Δ ε := Real.rpow_pos_of_pos hΔ_pos _
    have h8 : Real.rpow Δ (-ε) = (Real.rpow Δ ε)⁻¹ := rpow_neg' hΔ_pos
    rw [h8]
    have h9 : 1 ≤ (Real.rpow Δ ε)⁻¹ := by
      have h10 : (Real.rpow Δ ε)⁻¹ ≥ 1 := by
        calc (Real.rpow Δ ε)⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
             _ = 1 := by norm_num
      exact h10
    exact h9
  · have h_n_pos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    rcases polylog_absorption_real (A := (n : ℝ)) h_n_pos hε_pos with ⟨Δ₀, hΔ₀_pos, hΔ₀_le_one, h⟩
    refine ⟨Δ₀, hΔ₀_pos, hΔ₀_le_one, fun Δ hΔ_pos hΔ_le => ?_⟩
    have h_pos : 0 < Real.log (2 / Δ) := by
      have h1 : Δ ≤ 1 := by
        calc Δ ≤ Δ₀ := hΔ_le
             _ ≤ 1 := hΔ₀_le_one
      have h2 : (2 : ℝ) / Δ > 1 := by
        have h3 : Δ ≤ 1 := h1
        have h4 : (2 : ℝ) / Δ ≥ (2 : ℝ) / 1 := by
          gcongr
          <;> norm_num
        linarith
      exact Real.log_pos h2
    have h9 : (Real.log (2 / Δ)) ^ n = Real.rpow (Real.log (2 / Δ)) (n : ℝ) := by
      have h10 : Real.rpow (Real.log (2 / Δ)) (n : ℝ) = (Real.log (2 / Δ)) ^ n := by
        simp [Real.rpow_natCast] <;> norm_cast
      exact h10.symm
    rw [h9]
    exact h Δ hΔ_pos hΔ_le

/-- With multiplicative constant: C * (log(2/Δ))^A ≤ Δ^{-ε} for small Δ. -/
lemma polylog_absorption_with_const {C A ε : ℝ}
    (hA_pos : 0 < A) (hε_pos : 0 < ε) (hC_nonneg : 0 ≤ C) :
    ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ Δ₀ ≤ 1 ∧
      ∀ Δ : ℝ, 0 < Δ → Δ ≤ Δ₀ →
        C * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε) := by
  by_cases hC : C = 0
  · subst hC
    exact ⟨1, by norm_num, by norm_num, fun Δ _ _ => by simpa using Real.rpow_nonneg (by linarith) _⟩
  · have hC_pos : 0 < C := lt_of_le_of_ne hC_nonneg (Ne.symm hC)
    have hε2_pos : 0 < ε / 2 := by linarith
    rcases polylog_absorption_real hA_pos hε2_pos with ⟨Δ₁, hΔ₁_pos, hΔ₁_le_one, h1⟩
    let Δ₂ : ℝ := Real.rpow C (-(2 / ε))
    have hΔ₂_pos : 0 < Δ₂ := Real.rpow_pos_of_pos hC_pos _
    have h4 : Real.rpow Δ₂ (ε / 2) = C⁻¹ := by
      dsimp only [Δ₂]
      have h_pos1 : 0 < Real.rpow (Real.rpow C (-(2 / ε))) (ε / 2) :=
        Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hC_pos _) _
      have h_pos2 : 0 < C⁻¹ := by positivity
      have h_log_eq : Real.log (Real.rpow (Real.rpow C (-(2 / ε))) (ε / 2)) = Real.log (C⁻¹) := by
        have h_log1 : Real.log (Real.rpow (Real.rpow C (-(2 / ε))) (ε / 2)) =
            (ε / 2) * Real.log (Real.rpow C (-(2 / ε))) :=
          Real.log_rpow (Real.rpow_pos_of_pos hC_pos _) (ε / 2)
        have h_log2 : Real.log (Real.rpow C (-(2 / ε))) = (-(2 / ε)) * Real.log C := by
          have h' : Real.log (C ^ (-(2 / ε))) = (-(2 / ε)) * Real.log C :=
            Real.log_rpow hC_pos (-(2 / ε))
          exact h'
        have h_log3 : Real.log (C⁻¹) = -Real.log C := by
          simp [Real.log_inv] <;> ring
        calc Real.log (Real.rpow (Real.rpow C (-(2 / ε))) (ε / 2))
          = (ε / 2) * Real.log (Real.rpow C (-(2 / ε))) := h_log1
        _ = (ε / 2) * ((-(2 / ε)) * Real.log C) := by rw [h_log2]
        _ = -Real.log C := by field_simp [hε_pos.ne'] <;> ring
        _ = Real.log (C⁻¹) := by rw [h_log3]
      exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos1) (Set.mem_Ioi.mpr h_pos2) h_log_eq
    have hC_le : ∀ Δ : ℝ, 0 < Δ → Δ ≤ Δ₂ → C ≤ Real.rpow Δ (-(ε / 2)) := by
      intro Δ hΔ_pos hΔ_le
      have h3 : Real.rpow Δ (ε / 2) ≤ Real.rpow Δ₂ (ε / 2) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
      have h5 : Real.rpow Δ (ε / 2) ≤ C⁻¹ := by
        calc Real.rpow Δ (ε / 2) ≤ Real.rpow Δ₂ (ε / 2) := h3
             _ = C⁻¹ := h4
      have h6 : 0 < Real.rpow Δ (ε / 2) := Real.rpow_pos_of_pos hΔ_pos _
      have h7 : C * Real.rpow Δ (ε / 2) ≤ 1 := by
        calc C * Real.rpow Δ (ε / 2) ≤ C * C⁻¹ := by gcongr
             _ = 1 := by field_simp [hC_pos.ne'] <;> ring
      have h8 : C ≤ (Real.rpow Δ (ε / 2))⁻¹ := by
        have h10 : 0 < Real.rpow Δ (ε / 2) := h6
        calc C
          = C * Real.rpow Δ (ε / 2) / Real.rpow Δ (ε / 2) := by field_simp [h10.ne'] <;> ring
        _ ≤ 1 / Real.rpow Δ (ε / 2) := by gcongr
        _ = (Real.rpow Δ (ε / 2))⁻¹ := by ring
      have h12 : Real.rpow Δ (-(ε / 2)) = (Real.rpow Δ (ε / 2))⁻¹ := rpow_neg' hΔ_pos
      rw [h12]; exact h8
    let Δ₀ := min Δ₁ Δ₂
    have hΔ₀_pos : 0 < Δ₀ := by positivity
    have hΔ₀_le_one : Δ₀ ≤ 1 := by
      calc Δ₀ ≤ Δ₁ := min_le_left _ _
           _ ≤ 1 := hΔ₁_le_one
    refine ⟨Δ₀, hΔ₀_pos, hΔ₀_le_one, fun Δ hΔ_pos hΔ_le => ?_⟩
    have hΔ_le₁ : Δ ≤ Δ₁ := le_trans hΔ_le (min_le_left _ _)
    have hΔ_le₂ : Δ ≤ Δ₂ := le_trans hΔ_le (min_le_right _ _)
    have h3 : Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-(ε / 2)) := h1 Δ hΔ_pos hΔ_le₁
    have h4' : C ≤ Real.rpow Δ (-(ε / 2)) := hC_le Δ hΔ_pos hΔ_le₂
    have h_nonneg1 : 0 ≤ Real.rpow (Real.log (2 / Δ)) A := by
      apply Real.rpow_nonneg
      have h_pos : 0 < Real.log (2 / Δ) := by
        have h1 : Δ ≤ 1 := by
          calc Δ ≤ Δ₀ := hΔ_le
               _ ≤ 1 := hΔ₀_le_one
        have h2 : (2 : ℝ) / Δ > 1 := by
          have h3 : Δ ≤ 1 := h1
          have h4 : (2 : ℝ) / Δ ≥ 2 := by
            have h5 : 0 < Δ := hΔ_pos
            have h6 : Δ ≤ 1 := h3
            have h7 : (2 : ℝ) / Δ ≥ (2 : ℝ) / 1 := div_le_div_of_nonneg_left (by norm_num) (by positivity) h6
            norm_num at h7 ⊢ <;> exact h7
          linarith
        exact Real.log_pos h2
      exact h_pos.le
    have h_nonneg2 : 0 ≤ Real.rpow Δ (-(ε / 2)) := Real.rpow_nonneg (by linarith) _
    have h6 : C * Real.rpow (Real.log (2 / Δ)) A ≤
        Real.rpow Δ (-(ε / 2)) * Real.rpow Δ (-(ε / 2)) := by
      calc C * Real.rpow (Real.log (2 / Δ)) A
        ≤ Real.rpow Δ (-(ε / 2)) * Real.rpow (Real.log (2 / Δ)) A :=
          mul_le_mul_of_nonneg_right h4' h_nonneg1
      _ ≤ Real.rpow Δ (-(ε / 2)) * Real.rpow Δ (-(ε / 2)) :=
          mul_le_mul_of_nonneg_left h3 h_nonneg2
    have h_add : Real.rpow Δ (-(ε / 2)) * Real.rpow Δ (-(ε / 2)) = Real.rpow Δ (-ε) := by
      have h := rpow_add' (hx := hΔ_pos) (y := -(ε / 2)) (z := -(ε / 2))
      convert h using 1 <;> ring_nf
    rw [h_add] at h6
    exact h6

/-- Ember's K² absorption lemma: C * (log(2/δ))^C ≤ δ^{-β} for small δ.
  Handles all C ∈ ℝ: for C ≤ 0, LHS ≤ 0 < RHS; for C > 0, use polylog absorption. -/
lemma polylog_le_negative_power {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      C * (Real.log (2 / δ)) ^ C ≤ Real.rpow δ (-β) := by
  by_cases hC0 : C = 0
  · subst hC0
    refine ⟨1, by norm_num, fun δ hδ_pos _ => ?_⟩
    simpa using Real.rpow_nonneg (by linarith) _
  · have hC_pos : 0 < C := by
      exact lt_of_le_of_ne hC (Ne.symm hC0)
    rcases polylog_absorption_with_const (A := C) hC_pos hβ hC with
      ⟨δ₀, hδ₀_pos, hδ₀_le_one, h⟩
    refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
    have hδ_le : δ ≤ δ₀ := by linarith
    exact h δ hδ_pos hδ_le

end PolylogAbsorption
