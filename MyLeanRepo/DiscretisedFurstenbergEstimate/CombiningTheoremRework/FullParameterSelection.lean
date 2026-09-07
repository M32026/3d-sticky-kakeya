module

/-
  Complete parameter selection for theorem6_1_main_assembly.

  Provides ALL numeric parameters AND thresholds with REAL absorption bodies.

  Absorption clauses:
  - δ_app_sqrt: K_P factor δ_n^{-rho_sqrt} * 9 ≤ (9δ_n)^{-εA}
    where rho_sqrt = εReg + pointLoss (matches frontend K_P export)
  - δ_abs: point constant δ_n^{-(εReg+pointLoss)} * C_point_poly * n^d * 361 ≤ (9δ_n)^{-εA}
  - δ_B1: tube constant δ_n^{-(εReg+tubeLoss)} * C_tube_poly * n^d * 628849 * 44^s ≤ (9δ_n)^{-εA}
  - δ_front: 2 * C_geo_local * δ_front^heavyMargin < 1
  - δ_parent: C_parent_poly * n^degree_parent ≤ δ_n^{-loss_parent}
    (C_parent_poly should include D² = 262144², charged ONCE)

  Epsilon hierarchy: εInc = min(εReg/2, netGain/2).
  loss_B1 and loss_parent are SEPARATE line items in the budget, each subtracted once.

  Whiteprint node: theorem6_1_main_assembly / parameter_selection
  Status: COMPLETE — 0 sorrys
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.HeavyParentUniformClean
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate

/-- Doubling constant D for affine lines = 4^9 = 262144. -/
abbrev D_affine : ℕ := 262144

-- =====================================================================
-- Absorption helper lemmas (self-contained)
-- =====================================================================

/-- Absorb a positive constant C into δ^{-loss} for sufficiently small δ. -/
private lemma absorb_constant (C loss : ℝ) (hC_pos : 0 < C) (hloss_pos : 0 < loss) :
    ∃ (δR : ℝ), 0 < δR ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δR → C ≤ δ ^ (-loss) := by
  let δR : ℝ := C ^ (-1 / loss)
  have hδR_pos : 0 < δR := by positivity
  refine' ⟨δR, hδR_pos, _⟩
  intro δ hδ_pos hδ_le
  have h_exp_nonpos : -loss ≤ 0 := by linarith
  have h1 : δR ^ (-loss) ≤ δ ^ (-loss) :=
    Real.rpow_le_rpow_of_nonpos hδ_pos hδ_le h_exp_nonpos
  have h2 : δR ^ (-loss) = C := by
    dsimp only [δR]
    rw [← Real.rpow_mul hC_pos.le]
    have h3 : (-1 / loss) * (-loss) = 1 := by
      field_simp [hloss_pos.ne'] <;> ring
    rw [h3]; simp
  rw [h2] at h1
  exact h1

/-- Uniform polynomial-to-power absorption: C * n^d ≤ δ_n^{-loss} for small δ_n. -/
lemma uniform_polynomial_absorption
    (C : ℝ) (hC_nonneg : 0 ≤ C) (degree : ℕ)
    (loss : ℝ) (hloss_pos : 0 < loss) :
    ∃ (δR : ℝ), 0 < δR ∧
      ∀ (n : ℕ), dyadicDelta n ≤ δR →
        C * (n : ℝ)^degree ≤ (dyadicDelta n)^(-loss) := by
  by_cases hC : C = 0
  · refine' ⟨1 / 2, by norm_num, _⟩
    intro n hn
    rw [hC]
    have h : 0 ≤ (dyadicDelta n)^(-loss) := Real.rpow_nonneg (dyadicDelta_pos n).le _
    simpa using h
  · have hC_pos : 0 < C := lt_of_le_of_ne hC_nonneg (Ne.symm hC)
    let a : ℝ := loss * Real.log 2
    have ha_pos : 0 < a := by
      have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    have h3 : Filter.Tendsto (fun x : ℝ => Real.exp (a * x) / (a * x)^degree)
        Filter.atTop Filter.atTop :=
      (Real.tendsto_exp_div_pow_atTop degree).comp
        (Filter.tendsto_id.const_mul_atTop ha_pos)
    have h4 : Filter.Tendsto (fun x : ℝ => Real.exp (a * x) / x^degree)
        Filter.atTop Filter.atTop := by
      have h_ev : ∀ᶠ (x : ℝ) in Filter.atTop,
          a^degree * (Real.exp (a * x) / (a * x)^degree) = Real.exp (a * x) / x^degree := by
        filter_upwards [Filter.eventually_ge_atTop 1] with x hx
        have hx_pos : 0 < x := by linarith
        have ha_ne : a ≠ 0 := ha_pos.ne'
        have hx_ne : x ≠ 0 := hx_pos.ne'
        have h1 : (a * x)^degree = a^degree * x^degree := by ring
        rw [h1]
        field_simp [ha_ne, hx_ne] <;> ring
      exact (h3.const_mul_atTop (by positivity)).congr' h_ev
    have h5 : ∀ᶠ (x : ℝ) in Filter.atTop,
        Real.exp (a * x) / x^degree > C := by
      have h51 : Set.Ioi C ∈ Filter.atTop := by
        exact Filter.mem_atTop_sets.mpr ⟨C + 1, fun y hy => show C < y from by linarith⟩
      exact h4 h51
    rcases Filter.mem_atTop_sets.mp h5 with ⟨X1, hX1⟩
    let X : ℝ := max X1 1
    let N : ℕ := Nat.ceil X
    have hN_ge_X : (N : ℝ) ≥ X := Nat.le_ceil _
    have hN_pos : 0 < N := by
      have h1 : (N : ℝ) ≥ 1 := by
        have h2 : (1 : ℝ) ≤ X := le_max_right X1 1
        linarith [hN_ge_X]
      exact_mod_cast h1
    have h_bound : ∀ (n : ℕ), n ≥ N →
        (2 : ℝ)^((n : ℝ) * loss) > C * (n : ℝ)^degree := by
      intro n hn
      have h_n_ge_X : (n : ℝ) ≥ X := by
        have h : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
        linarith
      have h_ge_X1 : (n : ℝ) ≥ X1 := by
        have h2 : X ≥ X1 := le_max_left X1 1
        linarith
      have h_ge1 : (n : ℝ) ≥ 1 := by
        have h2 : X ≥ 1 := le_max_right X1 1
        linarith
      have h6 : Real.exp (a * (n : ℝ)) / (n : ℝ)^degree > C := hX1 (n : ℝ) h_ge_X1
      have h7 : 0 < (n : ℝ)^degree := by positivity
      have h8 : Real.exp (a * (n : ℝ)) > C * (n : ℝ)^degree := by
        have h_eq : Real.exp (a * (n : ℝ)) =
            (Real.exp (a * (n : ℝ)) / (n : ℝ)^degree) * (n : ℝ)^degree := by
          field_simp [h7.ne'] <;> ring
        rw [h_eq]; gcongr
      have h9 : Real.exp (a * (n : ℝ)) = (2 : ℝ)^((n : ℝ) * loss) := by
        have h10 : a * (n : ℝ) = (n : ℝ) * loss * Real.log 2 := by
          dsimp only [a] <;> ring
        rw [h10]
        have h11 : Real.exp ((n : ℝ) * loss * Real.log 2) =
            (Real.exp (Real.log 2))^((n : ℝ) * loss) := by
          rw [← Real.exp_mul] <;> ring_nf
        rw [h11]
        have h12 : Real.exp (Real.log 2) = 2 := by rw [Real.exp_log (by norm_num)]
        rw [h12] <;> ring
      rw [h9] at h8
      exact h8
    let δR : ℝ := dyadicDelta N
    have hδR_pos : 0 < δR := dyadicDelta_pos N
    have h_ge : ∀ (n : ℕ), dyadicDelta n ≤ δR → n ≥ N := by
      intro n h
      by_contra h'
      have h_lt : n < N := by omega
      have h9 : dyadicDelta n > dyadicDelta N := by
        dsimp only [dyadicDelta]
        have h10 : (2 : ℝ)^n < (2 : ℝ)^N := by
          have h13 : n < N := h_lt
          gcongr <;> norm_num
        have h11 : 0 < (2 : ℝ)^n := by positivity
        have h12 : 0 < (2 : ℝ)^N := by positivity
        exact one_div_lt_one_div_of_lt h11 h10
      linarith
    refine' ⟨δR, hδR_pos, _⟩
    intro n hn
    have h_n_ge_N : n ≥ N := h_ge n hn
    have h7 : (dyadicDelta n)^(-loss) = (2 : ℝ)^((n : ℝ) * loss) := by
      have h8 : dyadicDelta n = 1 / (2 : ℝ)^n := by
        simp [dyadicDelta] <;> ring
      rw [h8]
      have h9 : (1 / (2 : ℝ)^n)^(-loss) = (2 : ℝ)^((n : ℝ) * loss) := by
        have h10 : (1 / (2 : ℝ)^n) = (2 : ℝ)^(-(n : ℝ)) := by
          have h11 : (2 : ℝ)^n = (2 : ℝ)^(n : ℝ) := by norm_cast
          rw [h11, Real.rpow_neg (by positivity)] <;> field_simp
        rw [h10, ← Real.rpow_mul (by norm_num)] <;> ring_nf
      exact h9
    rw [h7]
    exact le_of_lt (h_bound n h_n_ge_N)

/-- Absorb δ_n^{-rho} * C_poly * n^degree into (9δ_n)^{-εA}. -/
private lemma absorb_power_times_polynomial
    (εA rho : ℝ) (hεA_pos : 0 < εA) (hrho_lt_εA : rho < εA)
    (C_poly : ℝ) (hC_poly_nonneg : 0 ≤ C_poly) (degree : ℕ) :
    ∃ (δR : ℝ), 0 < δR ∧
      ∀ (n : ℕ), dyadicDelta n ≤ δR →
        (dyadicDelta n)^(-rho) * C_poly * (n : ℝ)^degree ≤
        (9 * dyadicDelta n)^(-εA) := by
  have h_loss_pos : 0 < εA - rho := by linarith
  let C' : ℝ := C_poly * (9 : ℝ)^εA
  have hC'_nonneg : 0 ≤ C' := by positivity
  rcases uniform_polynomial_absorption C' hC'_nonneg degree (εA - rho) h_loss_pos
    with ⟨δR, hδR_pos, h_absorb⟩
  refine' ⟨δR, hδR_pos, _⟩
  intro n hn
  have h1 : C' * (n : ℝ)^degree ≤ (dyadicDelta n)^(-(εA - rho)) := h_absorb n hn
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h_product : (9 : ℝ)^(-εA) * (9 : ℝ)^εA = 1 := by
    have h : (9 : ℝ)^(-εA) * (9 : ℝ)^εA = (9 : ℝ)^((-εA) + εA) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 9)] <;> ring
    rw [h]
    have h2 : (-εA) + εA = 0 := by ring
    rw [h2] <;> simp
  have h2 : (9 * dyadicDelta n)^(-εA) =
      (9 : ℝ)^(-εA) * (dyadicDelta n)^(-εA) := by
    rw [Real.mul_rpow (by norm_num) hδ_pos.le]
  have h4 : C_poly * (9 : ℝ)^εA * (n : ℝ)^degree ≤
      (dyadicDelta n)^(-(εA - rho)) := by simpa [C'] using h1
  have h5 : C_poly * (n : ℝ)^degree ≤
      (9 : ℝ)^(-εA) * (dyadicDelta n)^(-(εA - rho)) := by
    have h51 : (9 : ℝ)^(-εA) * (C_poly * (9 : ℝ)^εA * (n : ℝ)^degree) ≤
        (9 : ℝ)^(-εA) * (dyadicDelta n)^(-(εA - rho)) := by gcongr
    have h52 : (9 : ℝ)^(-εA) * (C_poly * (9 : ℝ)^εA * (n : ℝ)^degree) =
        C_poly * (n : ℝ)^degree := by
      calc
        (9 : ℝ)^(-εA) * (C_poly * (9 : ℝ)^εA * (n : ℝ)^degree)
          = ((9 : ℝ)^(-εA) * (9 : ℝ)^εA) * (C_poly * (n : ℝ)^degree) := by ring
        _ = 1 * (C_poly * (n : ℝ)^degree) := by rw [h_product]
        _ = C_poly * (n : ℝ)^degree := by ring
    rw [← h52]; exact h51
  have h61 : 0 ≤ (dyadicDelta n)^(-rho) := by positivity
  have h6 : (dyadicDelta n)^(-rho) * C_poly * (n : ℝ)^degree ≤
      (dyadicDelta n)^(-rho) * ((9 : ℝ)^(-εA) * (dyadicDelta n)^(-(εA - rho))) := by
    have h_eq : (dyadicDelta n)^(-rho) * C_poly * (n : ℝ)^degree =
        (dyadicDelta n)^(-rho) * (C_poly * (n : ℝ)^degree) := by ring
    rw [h_eq]
    exact mul_le_mul_of_nonneg_left h5 h61
  have h71 : (dyadicDelta n)^(-rho) * (dyadicDelta n)^(-(εA - rho)) =
      (dyadicDelta n)^(-εA) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h7 : (dyadicDelta n)^(-rho) * ((9 : ℝ)^(-εA) * (dyadicDelta n)^(-(εA - rho))) =
      (9 : ℝ)^(-εA) * (dyadicDelta n)^(-εA) := by
    ring_nf at h71 ⊢ <;> rw [h71] <;> ring
  rw [h2]
  exact le_trans h6 (by rw [h7])

-- =====================================================================
-- Main theorem
-- =====================================================================

/-- Complete parameter selection with real absorption bodies.

  Takes worst-case polynomial bounds for point, tube, and parent constants.
  C_parent_poly should include D² = 262144² (geometry doubling), charged ONCE.

  Epsilon hierarchy: εInc = min(εReg/2, netGain/2), chosen AFTER εReg and netGain.

  loss_B1 and loss_parent are separate budget line items. -/
theorem complete_parameter_selection
    (εA s t : ℝ)
    (hεA_pos : 0 < εA) (hs : 0 < s) (hs1 : s < 1)
    (hst : s < t) (ht2 : t < 2)
    (C_point_poly C_tube_poly C_parent_poly : ℝ)
    (hC_point_nonneg : 0 ≤ C_point_poly)
    (hC_tube_nonneg : 0 ≤ C_tube_poly)
    (hC_parent_nonneg : 0 ≤ C_parent_poly)
    (degree_point degree_tube degree_parent : ℕ) :
    ∃ (εInc εReg fixedLoss pointLoss tubeLoss loss_B1 loss_parent
       coarseGain localLoss netGain lambda rho_M rho_mass rho_sqrt heavyMargin heavySlack
       coarsePointPolyLoss coarseTubePolyLoss coarseLogLoss
       finePointPolyLoss fineGlobalPolyLoss fineMarginLoss fineCQPolyLoss fineLogLoss
       pointRegularityLoss a_C_ret b_fine localFineLoss
       δ_front δ_abs δ_B1 δ_parent δ_app_sqrt : ℝ),
      0 < εInc ∧ εInc < εA ∧ εInc < εReg ∧ εInc < netGain ∧
      εInc ≤ εReg ∧ εInc ≤ netGain ∧
      0 < netGain ∧
      netGain ≤ coarseGain - localLoss - lambda - rho_M - loss_B1 - loss_parent ∧
      0 < εReg ∧ εReg < s ∧
      0 < fixedLoss ∧ 0 < pointLoss ∧ 0 < tubeLoss ∧
      εReg + pointLoss + tubeLoss + fixedLoss ≤ εA ∧
      0 < rho_mass ∧ 0 < rho_sqrt ∧ 0 < heavyMargin ∧
      heavySlack > rho_mass + rho_sqrt + heavyMargin ∧
      coarseGain ≤ εA * ((min t 1 - s) / (1 - s)) / 2 ∧
      εReg + fixedLoss ≤ lambda + rho_M ∧
      0 < δ_front ∧ 0 < δ_abs ∧ 0 < δ_B1 ∧ 0 < δ_parent ∧ 0 < δ_app_sqrt ∧
      -- SQRT ABSORPTION
      (∀ n, dyadicDelta n ≤ δ_app_sqrt →
        (dyadicDelta n)^(-rho_sqrt) * 9 ≤ (9 * dyadicDelta n)^(-εA)) ∧
      -- POINT ABSORPTION
      (∀ n, dyadicDelta n ≤ δ_abs →
        (dyadicDelta n)^(-(εReg + pointLoss)) * C_point_poly * (n : ℝ)^degree_point * 361 ≤
        (9 * dyadicDelta n)^(-εA)) ∧
      -- TUBE ABSORPTION
      (∀ n, dyadicDelta n ≤ δ_B1 →
        (dyadicDelta n)^(-(εReg + tubeLoss)) * C_tube_poly * (n : ℝ)^degree_tube * 628849 * (44 : ℝ)^s ≤
        (9 * dyadicDelta n)^(-εA)) ∧
      -- HEAVY ABSORPTION
      2 * C_geo_local * δ_front ^ heavyMargin < 1 ∧
      -- PARENT ABSORPTION (C_parent_poly includes D² = 262144², charged ONCE)
      (∀ n, dyadicDelta n ≤ δ_parent →
        C_parent_poly * (n : ℝ)^degree_parent ≤ (dyadicDelta n)^(-loss_parent)) ∧
      0 < loss_B1 ∧ 0 < loss_parent ∧ 0 < lambda ∧ 0 < rho_M ∧ 0 < localLoss ∧ loss_parent < εA ∧
      0 < coarsePointPolyLoss ∧ 0 < coarseTubePolyLoss ∧ 0 < coarseLogLoss ∧
      (2 * εReg + pointLoss + tubeLoss + coarseLogLoss < loss_parent / 2) ∧
      0 < finePointPolyLoss ∧ 0 < fineGlobalPolyLoss ∧ 0 < fineMarginLoss ∧
      0 < fineCQPolyLoss ∧ 0 < fineLogLoss ∧
      pointRegularityLoss = εReg + pointLoss + finePointPolyLoss ∧
      a_C_ret = pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt + fineMarginLoss ∧
      b_fine = εReg + tubeLoss + fineCQPolyLoss ∧
      localFineLoss = a_C_ret + b_fine + fineLogLoss ∧
      rho_sqrt = εReg + pointLoss ∧
      rho_sqrt ≤ rho_mass ∧
      localFineLoss < localLoss := by
  -- =====================================================================
  -- Numeric parameter selection
  -- =====================================================================
  let alpha0 : ℝ := (min t 1 - s) / (1 - s)
  have halpha0_pos : 0 < alpha0 := by
    dsimp only [alpha0]
    have h1 : s < min t 1 := lt_min hst hs1
    have h2 : 0 < 1 - s := by linarith
    exact div_pos (by linarith) h2

  let G : ℝ := εA * alpha0 / 2
  let coarseGain : ℝ := G
  let εReg : ℝ := min (s / 2) (G / 128)
  let fixedLoss : ℝ := G / 128
  let pointLoss : ℝ := G / 128
  let tubeLoss : ℝ := G / 128
  let localLoss : ℝ := G / 8
  let lambda : ℝ := G / 64
  let rho_M : ℝ := G / 64
  let loss_B1 : ℝ := G / 8
  let loss_parent : ℝ := G / 8
  let netGain : ℝ := G / 2
  let coarsePointPolyLoss : ℝ := G / 256
  let coarseTubePolyLoss : ℝ := G / 256
  let coarseLogLoss : ℝ := G / 256
  let finePointPolyLoss : ℝ := G / 256
  let fineGlobalPolyLoss : ℝ := G / 256
  let fineMarginLoss : ℝ := G / 256
  let fineCQPolyLoss : ℝ := G / 256
  let fineLogLoss : ℝ := G / 256
  let εInc : ℝ := min (εReg / 2) (netGain / 2)
  let rho_mass : ℝ := εA / 16
  let rho_sqrt : ℝ := εReg + pointLoss
  let heavyMargin : ℝ := εA / 16
  let heavySlack : ℝ := rho_mass + rho_sqrt + heavyMargin + εA / 16
  let pointRegularityLoss : ℝ := εReg + pointLoss + finePointPolyLoss
  let a_C_ret : ℝ := pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt + fineMarginLoss
  let b_fine : ℝ := εReg + tubeLoss + fineCQPolyLoss
  let localFineLoss : ℝ := a_C_ret + b_fine + fineLogLoss

  have hεReg_pos : 0 < εReg := by dsimp only [εReg]; positivity
  have hεReg_lt_s : εReg < s := by
    dsimp only [εReg]
    have h : min (s / 2) (G / 128) ≤ s / 2 := min_le_left _ _
    have h2 : s / 2 < s := by linarith [hs]
    linarith
  have hG_pos : 0 < G := by dsimp only [G, alpha0]; positivity
  have hcoarseGain_pos : 0 < coarseGain := by dsimp only [coarseGain]; exact hG_pos
  have halpha0_le_one : alpha0 ≤ 1 := by
    dsimp only [alpha0]
    have h1 : min t 1 ≤ 1 := min_le_right _ _
    have h2 : 0 < 1 - s := by linarith
    have h3 : min t 1 - s ≤ 1 - s := by linarith
    calc
      (min t 1 - s) / (1 - s) ≤ (1 - s) / (1 - s) := by gcongr
      _ = 1 := by field_simp [h2.ne']
  have hG_le_half_εA : G ≤ εA / 2 := by
    dsimp only [G]
    have h : alpha0 ≤ 1 := halpha0_le_one
    nlinarith [hεA_pos]
  have hcoarseGain_le_half_εA : coarseGain ≤ εA / 2 := by
    dsimp only [coarseGain]
    exact hG_le_half_εA
  have hεReg_lt_εA : εReg < εA := by
    dsimp only [εReg]
    have h : min (s / 2) (G / 128) ≤ G / 128 := min_le_right _ _
    have h2 : G / 128 < εA := by
      have h21 : G ≤ εA / 2 := hG_le_half_εA
      linarith [hεA_pos]
    linarith
  have hnetGain_pos : 0 < netGain := by dsimp only [netGain]; positivity
  have hεInc_pos : 0 < εInc := by dsimp only [εInc]; positivity
  have hεInc_lt_εReg : εInc < εReg := by
    dsimp only [εInc]
    have h : min (εReg / 2) (netGain / 2) ≤ εReg / 2 := min_le_left _ _
    have h2 : εReg / 2 < εReg := by linarith [hεReg_pos]
    linarith
  have hεInc_lt_netGain : εInc < netGain := by
    dsimp only [εInc]
    have h : min (εReg / 2) (netGain / 2) ≤ netGain / 2 := min_le_right _ _
    have h2 : netGain / 2 < netGain := by linarith [hnetGain_pos]
    linarith
  have hεInc_lt_εA : εInc < εA := by
    have h1 : εInc < εReg := hεInc_lt_εReg
    have h2 : εReg < εA := hεReg_lt_εA
    linarith
  have hbudget : netGain ≤ coarseGain - localLoss - lambda - rho_M - loss_B1 - loss_parent := by
    dsimp only [netGain, coarseGain, localLoss, lambda, rho_M, loss_B1, loss_parent]
    have hG_pos' : 0 < G := hG_pos
    linarith
  have hfixedLoss_pos : 0 < fixedLoss := by dsimp only [fixedLoss]; positivity
  have hpointLoss_pos : 0 < pointLoss := by dsimp only [pointLoss]; positivity
  have htubeLoss_pos : 0 < tubeLoss := by dsimp only [tubeLoss]; positivity
  have h_frontend_budget : εReg + pointLoss + tubeLoss + fixedLoss ≤ εA := by
    dsimp only [εReg, pointLoss, tubeLoss, fixedLoss]
    have h1 : min (s / 2) (G / 128) ≤ G / 128 := min_le_right _ _
    have h2 : G / 128 + G / 128 + G / 128 + G / 128 = G / 32 := by ring
    have h3 : G / 32 ≤ εA := by
      have h4 : G ≤ εA / 2 := hG_le_half_εA
      linarith [hεA_pos]
    linarith
  have hrho_mass_pos : 0 < rho_mass := by dsimp only [rho_mass]; positivity
  have hrho_sqrt_pos : 0 < rho_sqrt := by dsimp only [rho_sqrt]; positivity
  have hheavyMargin_pos : 0 < heavyMargin := by dsimp only [heavyMargin]; positivity
  have hheavySlack_gt : heavySlack > rho_mass + rho_sqrt + heavyMargin := by
    dsimp only [heavySlack, rho_mass, rho_sqrt, heavyMargin]; linarith [hεA_pos]
  have hcoarseGain_le : coarseGain ≤ εA * ((min t 1 - s) / (1 - s)) / 2 := by
    have h_eq : coarseGain = εA * ((min t 1 - s) / (1 - s)) / 2 := by
      simp only [coarseGain, G, alpha0]
      <;> ring
    rw [h_eq]
  have hloss_B1_pos : 0 < loss_B1 := by dsimp only [loss_B1]; positivity
  have hloss_parent_pos : 0 < loss_parent := by dsimp only [loss_parent]; positivity
  have hlambda_pos : 0 < lambda := by dsimp only [lambda]; positivity
  have hrho_M_pos : 0 < rho_M := by dsimp only [rho_M]; positivity
  have hlocalLoss_pos : 0 < localLoss := by dsimp only [localLoss]; positivity
  have hloss_parent_lt_εA : loss_parent < εA := by
    dsimp only [loss_parent]
    have h : G ≤ εA / 2 := hG_le_half_εA
    linarith [hεA_pos]
  have hrho_sqrt_lt_εA : rho_sqrt < εA := by
    dsimp only [rho_sqrt]
    have h : εReg + pointLoss + tubeLoss + fixedLoss ≤ εA := h_frontend_budget
    linarith [htubeLoss_pos, hfixedLoss_pos]
  have hcoarsePointPolyLoss_pos : 0 < coarsePointPolyLoss := by dsimp only [coarsePointPolyLoss]; positivity
  have hcoarseTubePolyLoss_pos : 0 < coarseTubePolyLoss := by dsimp only [coarseTubePolyLoss]; positivity
  have hcoarseLogLoss_pos : 0 < coarseLogLoss := by dsimp only [coarseLogLoss]; positivity
  have hfinePointPolyLoss_pos : 0 < finePointPolyLoss := by dsimp only [finePointPolyLoss]; positivity
  have hfineGlobalPolyLoss_pos : 0 < fineGlobalPolyLoss := by dsimp only [fineGlobalPolyLoss]; positivity
  have hfineMarginLoss_pos : 0 < fineMarginLoss := by dsimp only [fineMarginLoss]; positivity
  have hfineCQPolyLoss_pos : 0 < fineCQPolyLoss := by dsimp only [fineCQPolyLoss]; positivity
  have hfineLogLoss_pos : 0 < fineLogLoss := by dsimp only [fineLogLoss]; positivity
  have hpointRegularityLoss_def : pointRegularityLoss = εReg + pointLoss + finePointPolyLoss := by rfl
  have ha_C_ret_def : a_C_ret = pointRegularityLoss + fineGlobalPolyLoss + rho_sqrt + fineMarginLoss := by rfl
  have hb_fine_def : b_fine = εReg + tubeLoss + fineCQPolyLoss := by rfl
  have hlocalFineLoss_def : localFineLoss = a_C_ret + b_fine + fineLogLoss := by rfl
  have hrho_sqrt_eq : rho_sqrt = εReg + pointLoss := by rfl
  have hrho_sqrt_le_rho_mass : rho_sqrt ≤ rho_mass := by
    dsimp only [rho_sqrt, rho_mass]
    have h1 : εReg ≤ G / 128 := by
      dsimp only [εReg]; exact min_le_right _ _
    have h2 : pointLoss = G / 128 := by rfl
    have h3 : G ≤ εA / 2 := hG_le_half_εA
    have h4 : εReg + pointLoss ≤ G / 64 := by
      rw [h2]
      linarith [h1]
    have h5 : G / 64 ≤ εA / 16 := by
      linarith [h3, hG_pos]
    linarith
  have hlocalFineLoss_lt_localLoss : localFineLoss < localLoss := by
    dsimp only [localFineLoss, a_C_ret, b_fine, pointRegularityLoss, localLoss]
    dsimp only [rho_sqrt, finePointPolyLoss, fineGlobalPolyLoss, fineMarginLoss, fineCQPolyLoss, fineLogLoss]
    have hεReg_le : εReg ≤ G / 128 := by
      dsimp only [εReg]; exact min_le_right _ _
    have h_pointLoss : pointLoss = G / 128 := by rfl
    have h_tubeLoss : tubeLoss = G / 128 := by rfl
    rw [h_pointLoss, h_tubeLoss]
    linarith [hεReg_le, hG_pos]

  -- =====================================================================
  -- Absorption thresholds
  -- =====================================================================

  -- SQRT: absorb δ_n^{-rho_sqrt} * 9 into (9δ_n)^{-εA}
  rcases absorb_power_times_polynomial εA rho_sqrt hεA_pos hrho_sqrt_lt_εA 9 (by norm_num) 0
    with ⟨δ_app_sqrt, hδ_app_sqrt_pos, h_abs_sqrt_raw⟩
  have h_abs_sqrt : ∀ n, dyadicDelta n ≤ δ_app_sqrt →
      (dyadicDelta n)^(-rho_sqrt) * 9 ≤ (9 * dyadicDelta n)^(-εA) := by
    intro n hn
    have h := h_abs_sqrt_raw n hn
    have h9 : (n : ℝ)^0 = 1 := by simp
    rw [h9] at h
    simpa using h

  -- POINT: absorb δ_n^{-(εReg+pointLoss)} * C_point_poly * n^d * 361 into (9δ_n)^{-εA}
  let rho_point : ℝ := εReg + pointLoss
  have hrho_point_lt_εA : rho_point < εA := by
    dsimp only [rho_point]
    have h : εReg + pointLoss + tubeLoss + fixedLoss ≤ εA := h_frontend_budget
    linarith [htubeLoss_pos, hfixedLoss_pos]
  let C_point_total : ℝ := C_point_poly * 361
  have hC_point_total_nonneg : 0 ≤ C_point_total := by positivity
  rcases absorb_power_times_polynomial εA rho_point hεA_pos hrho_point_lt_εA C_point_total hC_point_total_nonneg degree_point
    with ⟨δ_abs, hδ_abs_pos, h_abs_point_raw⟩
  have h_abs_point : ∀ n, dyadicDelta n ≤ δ_abs →
      (dyadicDelta n)^(-(εReg + pointLoss)) * C_point_poly * (n : ℝ)^degree_point * 361 ≤
      (9 * dyadicDelta n)^(-εA) := by
    intro n hn
    have h := h_abs_point_raw n hn
    have h_eq : (dyadicDelta n)^(-(εReg + pointLoss)) * C_point_poly * (n : ℝ)^degree_point * 361 =
        (dyadicDelta n)^(-rho_point) * C_point_total * (n : ℝ)^degree_point := by
      dsimp only [C_point_total, rho_point] <;> ring
    rw [h_eq]
    exact h

  -- TUBE: absorb δ_n^{-(εReg+tubeLoss)} * C_tube_poly * n^d * 628849 * 44^s into (9δ_n)^{-εA}
  let rho_tube : ℝ := εReg + tubeLoss
  have hrho_tube_lt_εA : rho_tube < εA := by
    dsimp only [rho_tube]
    have h : εReg + pointLoss + tubeLoss + fixedLoss ≤ εA := h_frontend_budget
    linarith [hpointLoss_pos, hfixedLoss_pos]
  let C_tube_total : ℝ := C_tube_poly * 628849 * (44 : ℝ)^s
  have hC_tube_total_nonneg : 0 ≤ C_tube_total := by positivity
  rcases absorb_power_times_polynomial εA rho_tube hεA_pos hrho_tube_lt_εA C_tube_total hC_tube_total_nonneg degree_tube
    with ⟨δ_tube, hδ_tube_pos, h_abs_tube_raw⟩
  let δ_B1 : ℝ := δ_tube
  have hδ_B1_pos : 0 < δ_B1 := hδ_tube_pos
  have h_abs_tube : ∀ n, dyadicDelta n ≤ δ_B1 →
      (dyadicDelta n)^(-(εReg + tubeLoss)) * C_tube_poly * (n : ℝ)^degree_tube * 628849 * (44 : ℝ)^s ≤
      (9 * dyadicDelta n)^(-εA) := by
    intro n hn
    have h := h_abs_tube_raw n hn
    have h_eq : (dyadicDelta n)^(-(εReg + tubeLoss)) * C_tube_poly * (n : ℝ)^degree_tube * 628849 * (44 : ℝ)^s =
        (dyadicDelta n)^(-rho_tube) * C_tube_total * (n : ℝ)^degree_tube := by
      dsimp only [C_tube_total, rho_tube] <;> ring
    rw [h_eq]
    exact h

  -- HEAVY: choose δ_front so 2 * C_geo_local * δ_front^heavyMargin < 1
  let base : ℝ := 1 / (2 * C_geo_local + 1)
  have hbase_pos : 0 < base := by positivity
  let δ_front : ℝ := base ^ (1 / heavyMargin)
  have hδ_front_pos : 0 < δ_front := by dsimp only [δ_front]; positivity
  have hheavy_absorb : 2 * C_geo_local * δ_front ^ heavyMargin < 1 := by
    have h1 : δ_front ^ heavyMargin = base := by
      dsimp only [δ_front]
      rw [← Real.rpow_mul hbase_pos.le]
      have h2 : (1 / heavyMargin) * heavyMargin = 1 := by
        field_simp [show (heavyMargin : ℝ) ≠ 0 by linarith] <;> ring
      rw [h2, Real.rpow_one]
    rw [h1]
    dsimp only [base, C_geo_local] <;> norm_num

  -- PARENT: absorb C_parent_poly * n^degree_parent into δ_n^{-loss_parent}
  rcases uniform_polynomial_absorption C_parent_poly hC_parent_nonneg degree_parent loss_parent hloss_parent_pos
    with ⟨δ_parent, hδ_parent_pos, h_abs_parent⟩

  -- =====================================================================
  -- Package all parameters
  -- =====================================================================
  refine' ⟨εInc, εReg, fixedLoss, pointLoss, tubeLoss, loss_B1, loss_parent,
    coarseGain, localLoss, netGain, lambda, rho_M, rho_mass, rho_sqrt, heavyMargin, heavySlack,
    coarsePointPolyLoss, coarseTubePolyLoss, coarseLogLoss,
    finePointPolyLoss, fineGlobalPolyLoss, fineMarginLoss, fineCQPolyLoss, fineLogLoss,
    pointRegularityLoss, a_C_ret, b_fine, localFineLoss,
    δ_front, δ_abs, δ_B1, δ_parent, δ_app_sqrt, _⟩
  constructor
  · exact hεInc_pos
  constructor
  · exact hεInc_lt_εA
  constructor
  · exact hεInc_lt_εReg
  constructor
  · exact hεInc_lt_netGain
  constructor
  · exact le_of_lt hεInc_lt_εReg
  constructor
  · exact le_of_lt hεInc_lt_netGain
  constructor
  · exact hnetGain_pos
  constructor
  · exact hbudget
  constructor
  · exact hεReg_pos
  constructor
  · exact hεReg_lt_s
  constructor
  · exact hfixedLoss_pos
  constructor
  · exact hpointLoss_pos
  constructor
  · exact htubeLoss_pos
  constructor
  · exact h_frontend_budget
  constructor
  · exact hrho_mass_pos
  constructor
  · exact hrho_sqrt_pos
  constructor
  · exact hheavyMargin_pos
  constructor
  · exact hheavySlack_gt
  constructor
  · exact hcoarseGain_le
  constructor
  · have h1 : εReg ≤ G / 128 := by
      dsimp only [εReg]; exact min_le_right _ _
    have h2 : fixedLoss = G / 128 := by rfl
    have h3 : lambda = G / 64 := by rfl
    have h4 : rho_M = G / 64 := by rfl
    dsimp only [εReg, fixedLoss, lambda, rho_M]
    linarith [h1]
  constructor
  · exact hδ_front_pos
  constructor
  · exact hδ_abs_pos
  constructor
  · exact hδ_B1_pos
  constructor
  · exact hδ_parent_pos
  constructor
  · exact hδ_app_sqrt_pos
  constructor
  · exact h_abs_sqrt
  constructor
  · exact h_abs_point
  constructor
  · exact h_abs_tube
  constructor
  · exact hheavy_absorb
  constructor
  · exact h_abs_parent
  constructor
  · exact hloss_B1_pos
  constructor
  · exact hloss_parent_pos
  constructor
  · exact hlambda_pos
  constructor
  · exact hrho_M_pos
  constructor
  · exact hlocalLoss_pos
  constructor
  · exact hloss_parent_lt_εA
  constructor
  · exact hcoarsePointPolyLoss_pos
  constructor
  · exact hcoarseTubePolyLoss_pos
  constructor
  · exact hcoarseLogLoss_pos
  constructor
  · have hεReg_le : εReg ≤ G / 128 := by
      dsimp only [εReg]; exact min_le_right _ _
    have h_pointLoss : pointLoss = G / 128 := by rfl
    have h_tubeLoss : tubeLoss = G / 128 := by rfl
    have h_coarseLogLoss : coarseLogLoss = G / 256 := by rfl
    have h_loss_parent : loss_parent = G / 8 := by rfl
    rw [h_pointLoss, h_tubeLoss, h_coarseLogLoss, h_loss_parent]
    linarith [hεReg_le, hG_pos]
  constructor
  · exact hfinePointPolyLoss_pos
  constructor
  · exact hfineGlobalPolyLoss_pos
  constructor
  · exact hfineMarginLoss_pos
  constructor
  · exact hfineCQPolyLoss_pos
  constructor
  · exact hfineLogLoss_pos
  constructor
  · exact hpointRegularityLoss_def
  constructor
  · exact ha_C_ret_def
  constructor
  · exact hb_fine_def
  constructor
  · exact hlocalFineLoss_def
  constructor
  · exact hrho_sqrt_eq
  constructor
  · exact hrho_sqrt_le_rho_mass
  · exact hlocalFineLoss_lt_localLoss

/-- Reciprocal algebra adapter: from parent polynomial absorption to the
    geometry coefficient lower bound needed by coarse_data_from_b1.

    Given `10^80 * n^23 ≤ δ_n^(-loss_parent)`, prove
    `9^(-(s+εA)) / 262144^2 ≥ δ_n^(loss_parent)`.

    Proof:
      1. s + εA < 2  (since s < 1, εA < 1)
      2. 9^(s+εA) ≤ 9^2 = 81
      3. 81 * 262144^2 < 10^80  (numerical)
      4. 9^(s+εA) * 262144^2 ≤ 10^80 ≤ 10^80 * n^23  (n ≥ 1)
      5. 9^(s+εA) * 262144^2 ≤ δ_n^(-loss_parent)  (transitivity)
      6. Reciprocals: 9^(-(s+εA)) / 262144^2 ≥ δ_n^(loss_parent) -/
lemma parent_geometric_reciprocal_adapter
    {n : ℕ} {s εA loss_parent : ℝ}
    (hn_pos : 0 < n)
    (hs_lt_one : s < 1)
    (hεA_lt_one : εA < 1)
    (hδn_pos : 0 < dyadicDelta n)
    (hδn_lt_one : dyadicDelta n < 1)
    (h_abs_parent : (10 : ℝ)^80 * (n : ℝ)^23 ≤ (dyadicDelta n)^(-loss_parent)) :
    (9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2 ≥ (dyadicDelta n)^loss_parent := by
  have h_n_ge1 : (n : ℝ) ≥ 1 := by exact_mod_cast hn_pos
  have h_sum_lt_two : s + εA < 2 := by linarith
  have h1 : (9 : ℝ)^(s + εA) ≤ 81 := by
    have h : (9 : ℝ)^(s + εA) ≤ (9 : ℝ)^(2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (9 : ℝ)^(2 : ℝ) = 81 := by norm_num
    rw [h2] at h
    exact h
  have h3 : (81 : ℝ) * (262144 : ℝ)^2 < (10 : ℝ)^80 := by norm_num
  have h43 : (10 : ℝ)^80 ≤ (10 : ℝ)^80 * (n : ℝ)^23 := by
    have h_n23_ge1 : (n : ℝ)^23 ≥ 1 := by
      have h : (n : ℝ) ≥ 1 := h_n_ge1
      have h5 : (n : ℝ)^23 ≥ 1^23 := by gcongr
      simpa using h5
    have h_pos : (0 : ℝ) < (10 : ℝ)^80 := by positivity
    nlinarith
  have h4 : (9 : ℝ)^(s + εA) * (262144 : ℝ)^2 ≤ (10 : ℝ)^80 * (n : ℝ)^23 := by
    have h41 : (9 : ℝ)^(s + εA) * (262144 : ℝ)^2 ≤ 81 * (262144 : ℝ)^2 := by
      gcongr <;> linarith
    have h42 : 81 * (262144 : ℝ)^2 ≤ (10 : ℝ)^80 := by exact h3.le
    calc (9 : ℝ)^(s + εA) * (262144 : ℝ)^2
      ≤ 81 * (262144 : ℝ)^2 := h41
    _ ≤ (10 : ℝ)^80 := h42
    _ ≤ (10 : ℝ)^80 * (n : ℝ)^23 := h43
  have h5 : (9 : ℝ)^(s + εA) * (262144 : ℝ)^2 ≤ (dyadicDelta n)^(-loss_parent) :=
    le_trans h4 h_abs_parent
  have h_pos1 : 0 < (9 : ℝ)^(s + εA) * (262144 : ℝ)^2 := by positivity
  have h_pos2 : 0 < (dyadicDelta n)^(-loss_parent) := Real.rpow_pos_of_pos hδn_pos _
  have h6 : 1 / ((9 : ℝ)^(s + εA) * (262144 : ℝ)^2) ≥
      1 / (dyadicDelta n)^(-loss_parent) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h5
  have h7 : 1 / ((9 : ℝ)^(s + εA) * (262144 : ℝ)^2) =
      (9 : ℝ)^(-(s + εA)) / (262144 : ℝ)^2 := by
    have h8 : (9 : ℝ)^(-(s + εA)) = 1 / (9 : ℝ)^(s + εA) := by
      rw [Real.rpow_neg (by norm_num)] <;> ring
    rw [h8] <;> field_simp <;> ring
  have h91 : (dyadicDelta n)^(-loss_parent) = 1 / (dyadicDelta n)^loss_parent := by
    rw [Real.rpow_neg hδn_pos.le] <;> ring
  have h9 : 1 / (dyadicDelta n)^(-loss_parent) = (dyadicDelta n)^loss_parent := by
    rw [h91]
    have h_pos3 : 0 < (dyadicDelta n)^loss_parent := Real.rpow_pos_of_pos hδn_pos _
    field_simp [h_pos3.ne'] <;> ring
  rw [h7, h9] at h6
  exact h6

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
