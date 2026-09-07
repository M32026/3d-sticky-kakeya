import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44QuarterDirect
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44QuarterDyadic
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma44QuarterDelta0

/-!
WZ1 Lemma 44: turn line non-concentration and Frostman bounds into a
one-quarter discrete thin-tubes relation after removing few bad pairs.
-/

namespace Kakeya.Assouad

theorem wz1_quarter_thin_tubes :
    WZ1QuarterThinTubesStatement := by
  intro lambda zeta alpha hlambda hzeta halpha
  by_cases h_main : zeta ≥ 1 / 4 ∨ 12 * alpha / zeta + 4 * lambda ≥ 1
  · -- DIRECT CASE
    refine ⟨1 / 2, by norm_num, by norm_num, fun delta hdelta hdelta_le => ?_⟩
    intro G₁ G₂ hG1ne hG2ne hG1ball hG2ball hG1sep hG2sep hFrost1 hFrost2 hMutSep hNonConc
    have hdelta1 : delta < 1 := by linarith
    exact wz1_quarter_direct_bound (G₁ := G₁) (G₂ := G₂) hdelta hdelta1 hlambda hzeta halpha hG1ne hG2ne hNonConc h_main
  · -- DYADIC CASE
    have hzeta_small : zeta < 1 / 4 := by
      by_contra h
      have h' : zeta ≥ 1 / 4 := by linarith
      exact h_main (Or.inl h')
    have hE_small : 12 * alpha / zeta + 4 * lambda < 1 := by
      by_contra h
      have h' : 12 * alpha / zeta + 4 * lambda ≥ 1 := by linarith
      exact h_main (Or.inr h')
    set E : ℝ := 12 * alpha / zeta + 4 * lambda with hE
    set K_exp : ℝ := 3 * alpha / zeta + lambda with hK_exp
    set D2 : ℝ := 8 * alpha / zeta + 2 * lambda - 4 * alpha with hD2
    set D3 : ℝ := 8 * alpha / zeta + lambda - 8 * alpha with hD3
    have hE_pos : 0 < E := by positivity
    have hK_exp_pos : 0 < K_exp := by positivity
    have hD2_pos : 0 < D2 := D2_pos halpha hlambda hzeta hzeta_small
    have hD3_pos : 0 < D3 := D3_pos halpha hlambda hzeta hzeta_small
    -- Log absorption
    rcases quarter_thin_tubes_log_absorption (2 * Real.sqrt 312002) alpha (by positivity) halpha with
      ⟨δ₀_abs, hδ₀_abs_pos, hδ₀_abs_one, h_abs_lemma⟩
    -- Bound constants
    let b1 : ℝ := Real.rpow 2 (-(1 / (4 * K_exp)))
    let b2 : ℝ := Real.rpow (1 / 26) (1 / E)
    let b3 : ℝ := Real.rpow (1 / 208) (1 / D2)
    let b4 : ℝ := Real.rpow (1 / 624000) (1 / D3)
    let inner : ℝ := min (min (min b1 b2) b3) b4
    let δ₀ : ℝ := min inner δ₀_abs
    have hb1_pos : 0 < b1 := Real.rpow_pos_of_pos (by norm_num) _
    have hb2_pos : 0 < b2 := Real.rpow_pos_of_pos (by norm_num) _
    have hb3_pos : 0 < b3 := Real.rpow_pos_of_pos (by norm_num) _
    have hb4_pos : 0 < b4 := Real.rpow_pos_of_pos (by norm_num) _
    have hinner_pos : 0 < inner := by dsimp only [inner] <;> positivity
    have hδ₀_pos : 0 < δ₀ := by dsimp only [δ₀] <;> positivity
    have h_b1_lt_one : b1 < 1 := by
      dsimp only [b1]
      set y : ℝ := 1 / (4 * K_exp) with hy_def
      have hy_pos : 0 < y := by positivity
      have h1 : 1 < Real.rpow 2 y := Real.one_lt_rpow (by norm_num) hy_pos
      have h2 : Real.rpow 2 (-y) = (Real.rpow 2 y)⁻¹ := Real.rpow_neg (by norm_num) y
      rw [h2]
      have h5 : 0 < Real.rpow 2 y := by positivity
      have h6 : (Real.rpow 2 y)⁻¹ < 1 := by
        calc (Real.rpow 2 y)⁻¹
          = 1 / (Real.rpow 2 y) := by simp
        _ < 1 / 1 := by gcongr
        _ = 1 := by norm_num
      exact h6
    have hinner_le_b1 : inner ≤ b1 := by
      dsimp only [inner]
      exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have hδ₀_lt_one : δ₀ < 1 := by
      dsimp only [δ₀]
      have h1 : δ₀ ≤ inner := min_le_left _ _
      exact lt_of_le_of_lt h1 (lt_of_le_of_lt hinner_le_b1 h_b1_lt_one)
    have hδ₀_one : δ₀ ≤ 1 := hδ₀_lt_one.le
    refine ⟨δ₀, hδ₀_pos, hδ₀_one, fun delta hdelta hdelta_le => ?_⟩
    intro G₁ G₂ hG1ne hG2ne hG1ball hG2ball hG1sep hG2sep hFrost1 hFrost2 hMutSep hNonConc
    have hdelta1 : delta < 1 := by
      calc delta ≤ δ₀ := hdelta_le
           _ < 1 := hδ₀_lt_one
    have hδ₀_le_inner : δ₀ ≤ inner := by dsimp only [δ₀] <;> exact min_le_left _ _
    have hinner_le_b2 : inner ≤ b2 := by
      dsimp only [inner]
      exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    have hinner_le_b3 : inner ≤ b3 := by
      dsimp only [inner]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hinner_le_b4 : inner ≤ b4 := by
      dsimp only [inner]
      exact min_le_right _ _
    have hb1 : delta ≤ b1 := le_trans hdelta_le (le_trans hδ₀_le_inner hinner_le_b1)
    have hb2 : delta ≤ b2 := le_trans hdelta_le (le_trans hδ₀_le_inner hinner_le_b2)
    have hb3 : delta ≤ b3 := le_trans hdelta_le (le_trans hδ₀_le_inner hinner_le_b3)
    have hb4 : delta ≤ b4 := le_trans hdelta_le (le_trans hδ₀_le_inner hinner_le_b4)
    have hb_abs : delta ≤ δ₀_abs := le_trans hdelta_le (by dsimp only [δ₀] <;> exact min_le_right _ _)
    let T := Real.rpow delta E
    let T' := 2 * T
    let scales := dyadic_scale_family delta T'
    have hT_gt_delta : delta < T := by
      have h : Real.rpow delta 1 < Real.rpow delta E :=
        Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 hE_small
      have h' : Real.rpow delta 1 = delta := by simp
      rw [h'] at h
      exact h
    have hT_pos : 0 < T := Real.rpow_pos_of_pos hdelta E
    have hT'_gt_delta : delta < T' := by
      dsimp only [T']
      linarith
    -- Arithmetic premises
    have hK_ge_one : 1 ≤ Real.rpow delta (-K_exp) / Real.rpow 2 (1 / 4 : ℝ) :=
      K_ge_one_of_bound hdelta hK_exp_pos hb1
    have hb2' : Real.rpow delta E ≤ 1 / 26 :=
      rpow_bound_of_le hdelta (by norm_num) (by norm_num) hE_pos hb2
    have hT'_le : T' ≤ 1 / 13 := by
      dsimp only [T', T]
      linarith
    have hscale1 : ∀ R ∈ scales, R ≤ 1 := by
      intro R hR
      have h : R < T' := dyadic_scale_family.all_lt_T hdelta hT'_gt_delta hR
      linarith [hT'_le]
    have h13scale : ∀ R ∈ scales, 13 * R ≤ 1 := by
      intro R hR
      have h : R < T' := dyadic_scale_family.all_lt_T hdelta hT'_gt_delta hR
      linarith [hT'_le]
    have hb3' : Real.rpow delta D2 ≤ 1 / 208 :=
      rpow_bound_of_le hdelta (by norm_num) (by norm_num) hD2_pos hb3
    have h_exp2 : E = D2 + (lambda + 4 * alpha + lambda + 4 * alpha / zeta) := by
      dsimp only [D2, E] <;> field_simp [hzeta.ne'] <;> ring
    have hprem2 : ∀ R ∈ scales,
        8 * (13 * R) ≤ Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
      intro R hR
      have hR_lt_T' : R < T' := dyadic_scale_family.all_lt_T hdelta hT'_gt_delta hR
      have h1 : 8 * (13 * R) < 208 * T := by
        dsimp only [T'] at hR_lt_T'
        linarith
      set X : ℝ := (lambda + 4 * alpha) + (lambda + 4 * alpha / zeta) with hX_def
      have h_T_expand : T = Real.rpow delta D2 * Real.rpow delta X := by
        dsimp only [T]
        have h_eq : E = D2 + X := by rw [h_exp2, hX_def] <;> ring
        rw [h_eq]
        exact Real.rpow_add hdelta D2 X
      have h_rpow_X : Real.rpow delta X = Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
        have hX_eq : X = (lambda + 4 * alpha) + (lambda + 4 * alpha / zeta) := by
          rw [hX_def] <;> ring
        rw [hX_eq]
        exact Real.rpow_add hdelta (lambda + 4 * alpha) (lambda + 4 * alpha / zeta)
      have h5 : 208 * T ≤ Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
        rw [h_T_expand, h_rpow_X]
        have h9 : 208 * Real.rpow delta D2 ≤ 1 := by linarith [hb3']
        have h10 : 0 ≤ Real.rpow delta D2 := Real.rpow_nonneg hdelta.le _
        have h11 : 0 ≤ Real.rpow delta (lambda + 4 * alpha) * Real.rpow delta (lambda + 4 * alpha / zeta) := by
          apply mul_nonneg <;> exact Real.rpow_nonneg hdelta.le _
        nlinarith
      linarith
    have hb4' : Real.rpow delta D3 ≤ 1 / 624000 :=
      rpow_bound_of_le hdelta (by norm_num) (by norm_num) hD3_pos hb4
    have h_exp3 : 4 * K_exp = 12 * alpha / zeta + 4 * lambda := by
      dsimp only [K_exp] <;> ring
    have hD3_eq : D3 + 4 * alpha = 8 * alpha / zeta + lambda - 4 * alpha := by
      dsimp only [D3] <;> ring
    have hK_exp_def : K_exp = 3 * alpha / zeta + lambda := by
      dsimp only [K_exp] <;> ring
    have hD3_def : D3 = 8 * alpha / zeta + lambda - 8 * alpha := by
      dsimp only [D3] <;> ring
    have hprem3 :
        (312000 : ℝ) / (Real.rpow delta (-K_exp) / Real.rpow 2 (1 / 4 : ℝ)) ^ 4 *
          Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) ≤
        Real.rpow delta (4 * alpha) :=
      prem3_bound hdelta hlambda hzeta halpha hK_exp_pos hD3_pos hK_exp_def hD3_def hb4'
    -- Absorption
    have h_absorb : (Real.sqrt 312002 * (scales.card : ℝ)) * Real.rpow delta (2 * alpha) ≤
        Real.rpow delta alpha := by
      have hT_lt_one : T < 1 := by
        dsimp only [T]
        have h : Real.rpow delta E < Real.rpow delta 0 :=
          Real.rpow_lt_rpow_of_exponent_gt hdelta hdelta1 hE_pos
        have h' : Real.rpow delta 0 = 1 := by simp
        rw [h'] at h
        exact h
      have h_card : (scales.card : ℝ) ≤ Real.logb 2 (1 / delta) + 2 := by
        have h_card_eq : scales.card = Nat.ceil (Real.logb 2 (T' / delta)) :=
          dyadic_scale_family.card hdelta hT'_gt_delta
        have h1 : (scales.card : ℝ) ≤ Real.logb 2 (T' / delta) + 1 := by
          rw [h_card_eq]
          exact dyadic_scale_family.N_bound hdelta hT'_gt_delta
        have h2 : T' / delta < 2 / delta := by
          dsimp only [T']
          have hT_pos' : 0 < T := hT_pos
          gcongr <;> linarith
        have h3 : 0 < T' / delta := by positivity
        have h4 : Real.logb 2 (T' / delta) < Real.logb 2 (2 / delta) :=
          Real.logb_lt_logb (by norm_num) h3 h2
        have h5 : Real.logb 2 (2 / delta) = Real.logb 2 (1 / delta) + 1 := by
          have h6 : (2 / delta : ℝ) = 2 * (1 / delta) := by ring
          rw [h6]
          rw [Real.logb_mul (by norm_num) (by positivity)]
          have h7 : Real.logb 2 2 = 1 := by
            have h8 : Real.logb 2 2 = Real.log 2 / Real.log 2 := by rfl
            rw [h8]
            have h9 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            field_simp [h9.ne'] <;> ring
          rw [h7] <;> ring
        linarith
      have h_main_abs : (2 * Real.sqrt 312002) * (Real.logb 2 (1 / delta) + 1) *
          Real.rpow delta (2 * alpha) ≤ Real.rpow delta alpha :=
        h_abs_lemma delta hdelta hb_abs
      have h17 : 0 ≤ Real.logb 2 (1 / delta) := by
        have h18 : 1 ≤ 1 / delta := by
          rw [one_le_div hdelta] <;> exact hdelta1.le
        exact Real.logb_nonneg (by norm_num) h18
      have h18 : (Real.sqrt 312002 * (scales.card : ℝ)) ≤
          (2 * Real.sqrt 312002) * (Real.logb 2 (1 / delta) + 1) := by
        have h19 : (scales.card : ℝ) ≤ Real.logb 2 (1 / delta) + 2 := h_card
        have h20 : Real.sqrt 312002 * (scales.card : ℝ) ≤
            Real.sqrt 312002 * (Real.logb 2 (1 / delta) + 2) :=
          mul_le_mul_of_nonneg_left h19 (by positivity)
        have h21 : Real.logb 2 (1 / delta) + 2 ≤ 2 * (Real.logb 2 (1 / delta) + 1) := by linarith
        have h22 : 0 ≤ Real.sqrt 312002 := by positivity
        calc
          Real.sqrt 312002 * (scales.card : ℝ)
            ≤ Real.sqrt 312002 * (Real.logb 2 (1 / delta) + 2) := h20
          _ ≤ Real.sqrt 312002 * (2 * (Real.logb 2 (1 / delta) + 1)) :=
            mul_le_mul_of_nonneg_left h21 h22
          _ = (2 * Real.sqrt 312002) * (Real.logb 2 (1 / delta) + 1) := by ring
      have h23 : 0 ≤ Real.rpow delta (2 * alpha) := Real.rpow_nonneg (by linarith) _
      calc
        (Real.sqrt 312002 * (scales.card : ℝ)) * Real.rpow delta (2 * alpha)
          ≤ ((2 * Real.sqrt 312002) * (Real.logb 2 (1 / delta) + 1)) * Real.rpow delta (2 * alpha) :=
            mul_le_mul_of_nonneg_right h18 h23
        _ = (2 * Real.sqrt 312002) * (Real.logb 2 (1 / delta) + 1) * Real.rpow delta (2 * alpha) := by ring
        _ ≤ Real.rpow delta alpha := h_main_abs
    have hK_ge_one' : 1 ≤ Real.rpow delta (-3 * alpha / zeta - lambda) / Real.rpow 2 (1 / 4 : ℝ) := by
      have h_eq : -3 * alpha / zeta - lambda = -K_exp := by
        simp [hK_exp] <;> ring
      rw [h_eq]
      exact hK_ge_one
    have hprem3' : (312000 : ℝ) / (Real.rpow delta (-3 * alpha / zeta - lambda) / Real.rpow 2 (1 / 4 : ℝ)) ^ 4 *
          Real.rpow delta (-(3 * lambda + 4 * alpha + 4 * alpha / zeta)) ≤
        Real.rpow delta (4 * alpha) := by
      have h_eq : -3 * alpha / zeta - lambda = -K_exp := by
        dsimp only [K_exp] <;> ring
      rw [h_eq]
      exact hprem3
    exact dyadic_assembly_main
      hdelta hdelta1 hlambda hzeta halpha hzeta_small hE_small
      hG1ne hG2ne hG1ball hG2ball hG1sep hG2sep hFrost1 hFrost2 hMutSep hNonConc
      hK_ge_one' hscale1 h13scale hprem2 hprem3' h_absorb

end Kakeya.Assouad
