module

/-
  Section 9 main theorem — thin wrapper around step5_source_faithful_v8.

  Selects parameters (ε_G, η, ε_N, B_K, ε_K, ε_Root, Δ, q), calls
  multiscaleDecompKaufman for the root decomposition, then invokes
  step5_source_faithful_v8 with ε_section9 = ε_Root/4, ε_target = ε_Root/8,
  reserved_budget = ε_Root/8, K_plane = K_affine = 1.

  Weakens source S-sets from ε_final to ε_input and returns the final
  Ncover lower bound at exponent ε_final = min ε_input ε_target.

  Whiteprint node: section9 / section9_main
  Dependencies: Section9Assembly (step5_source_faithful_v8),
                MultiscaleDecomposition.Root (multiscaleDecompKaufman),
                Contracts.Prop73 (prop73_main)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.Section9Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Root
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.Theorem61UniformData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.Prop73
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

set_option maxHeartbeats 2000000

namespace DirecretisedFurstenbergEstimate.Section9Assembly

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open MultiscaleDecomposition

theorem section9_main
    (s t : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (ε_inc : ℝ) (hε_inc_pos : 0 < ε_inc)
    (h_uniform : UniformIncidenceData s t ε_inc) :
    ∃ (ε_final : ℝ), 0 < ε_final ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
          ∀ (P : Set EuclideanPlane),
            P ⊆ Metric.closedBall 0 1 →
            IsDeltaSSet δ t (Real.rpow δ (-ε_final)) P →
            ∀ (T : Set AffineLine)
              (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine),
              (∀ p hp, Tp p hp ⊆ T) →
              (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_final)) (Tp p hp)) →
              (∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1) →
              Ncover δ T ≥
                ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_final))) := by

  -- ========================================================================
  -- Step 0: Uniform combining induction from Prop 7.3
  -- ========================================================================
  rcases prop73_main s hs hs1 with ⟨K, hK_ge1, H_all⟩
  have H_uniform : CombiningInductionUniform_with_data_bounded s t ε_inc K :=
    H_all t ε_inc hst ht2 hε_inc_pos
  rcases H_uniform hK_ge1 with ⟨ε_G0, η0, hεG0_pos, hη0_pos, hsmall, H_main⟩

  -- ========================================================================
  -- Step 1: Exponent selection
  -- ========================================================================
  let ε_G : ℝ := min (ε_G0 / 2) ((t - s) / 2)
  have hεG_pos : 0 < ε_G := by positivity
  have hεG_le : ε_G ≤ ε_G0 := by
    dsimp only [ε_G]
    calc min (ε_G0 / 2) ((t - s) / 2) ≤ ε_G0 / 2 := min_le_left _ _
      _ ≤ ε_G0 := by linarith
  have hεG_small : ε_G < 2 * (t - s) := by
    dsimp only [ε_G]
    have h : min (ε_G0 / 2) ((t - s) / 2) ≤ (t - s) / 2 := min_le_right _ _
    linarith
  have hεG_le_one : ε_G ≤ 1 := by
    dsimp only [ε_G]
    have h1 : (t - s) / 2 < 1 := by linarith
    have h2 : min (ε_G0 / 2) ((t - s) / 2) ≤ (t - s) / 2 := min_le_right _ _
    linarith

  let η_K_max : ℝ := (t - s) / ((1 + 6 / (t - s)) * ε_G)
  have hηK_max_pos : 0 < η_K_max := by positivity
  let η : ℝ := min (η0 / 2) (min 1 (η_K_max / 2))
  have hη_pos : 0 < η := by positivity
  have hη_le : η ≤ η0 := by
    dsimp only [η]
    calc min (η0 / 2) (min 1 (η_K_max / 2)) ≤ η0 / 2 := min_le_left _ _
      _ ≤ η0 := by linarith
  have hη_le_one : η ≤ 1 := by
    dsimp only [η]
    calc min (η0 / 2) (min 1 (η_K_max / 2)) ≤ min 1 (η_K_max / 2) := min_le_right _ _
      _ ≤ 1 := min_le_left _ _

  let ε_N : ℝ := ε_G * η / 100
  have hεN_pos : 0 < ε_N := by positivity
  have hεN_le_εG : ε_N ≤ ε_G := by
    dsimp only [ε_N]
    have h2 : η ≤ 1 := hη_le_one
    have h3 : ε_G * η ≤ ε_G := by
      calc ε_G * η ≤ ε_G * (1 : ℝ) := by gcongr
        _ = ε_G := by ring
    have h4 : ε_G * η / 100 ≤ ε_G := by
      calc ε_G * η / 100 ≤ ε_G / 100 := by gcongr
        _ ≤ ε_G := by linarith [hεG_pos]
    exact h4
  have hεN_eq : ε_N = ε_G * η / 100 := by rfl

  let B_K : ℝ := 3 + 12 / (t - s)
  have hB_K_ge3 : B_K ≥ 3 := by
    dsimp only [B_K]
    have h_pos : 0 < t - s := by linarith [hst]
    have h2 : 0 ≤ 12 / (t - s) := by positivity
    linarith
  have hB_K_pos : 0 < B_K := by positivity

  let ε_K : ℝ := ε_N / (2 * B_K)
  have hεK_pos : 0 < ε_K := by positivity

  let ε_Root : ℝ := ε_K / 2
  have hε_Root_pos : 0 < ε_Root := by positivity
  have hε_Root_eq : ε_Root = ε_N / (4 * B_K) := by
    dsimp only [ε_Root, ε_K]
    field_simp [hB_K_pos.ne'] <;> ring

  -- Output exponents for v8
  let ε_section9 : ℝ := ε_Root / 4
  let ε_target : ℝ := ε_Root / 8
  let reserved_budget : ℝ := ε_Root / 8
  have hε_section9_pos : 0 < ε_section9 := by positivity
  have hε_target_pos : 0 < ε_target := by positivity
  have hε_target_lt_section9 : ε_target < ε_section9 := by
    dsimp only [ε_target, ε_section9]
    linarith [hε_Root_pos]
  have hbudget_pos : 0 < reserved_budget := by positivity
  have hε_section9_le : ε_section9 ≤ ε_N / (16 * B_K) := by
    dsimp only [ε_section9, ε_Root, ε_K]
    have h : ε_N / (2 * B_K) / 2 / 4 = ε_N / (16 * B_K) := by
      field_simp [hB_K_pos.ne'] <;> ring
    rw [h]

  let K_plane : ℝ := 1
  let K_affine : ℝ := 1
  have hK_plane_ge1 : 1 ≤ K_plane := by norm_num
  have hK_affine_ge1 : 1 ≤ K_affine := by norm_num

  -- ========================================================================
  -- Step 2: Kaufman smallness condition
  -- ========================================================================
  have hKaufman_small_εN : (1 + 6 / (t - s)) * ε_N < t - s := by
    have h1 : η ≤ η_K_max / 2 := by
      calc min (η0 / 2) (min 1 (η_K_max / 2)) ≤ min 1 (η_K_max / 2) := min_le_right _ _
        _ ≤ η_K_max / 2 := min_le_right _ _
    have h2 : (1 + 6 / (t - s)) * (ε_G * η / 100) ≤
        (1 + 6 / (t - s)) * (ε_G * (η_K_max / 2) / 100) := by gcongr <;> linarith
    have hts_pos : 0 < t - s := by linarith
    have h3 : (1 + 6 / (t - s)) * (ε_G * (η_K_max / 2) / 100) = (t - s) / 200 := by
      dsimp only [η_K_max]
      field_simp [hts_pos.ne'] <;> ring
    rw [h3] at h2
    have h4 : (t - s) / 200 < t - s := by
      have h5 : 0 < t - s := hts_pos
      have h6 : (1 : ℝ) < 200 := by norm_num
      exact div_lt_self h5 h6
    exact lt_of_le_of_lt h2 h4

  -- Quantitative bridge: ε_K < ε_N, so Kaufman smallness for ε_K follows from ε_N
  have hεK_lt_εN : ε_K < ε_N := by
    dsimp only [ε_K]
    have h1 : 1 < 2 * B_K := by linarith [hB_K_ge3]
    exact div_lt_self hεN_pos h1
  have hKaufman_small : (1 + 6 / (t - s)) * ε_K < t - s := by
    have h1 : (1 + 6 / (t - s)) * ε_K < (1 + 6 / (t - s)) * ε_N := by
      have hpos : 0 < 1 + 6 / (t - s) := by positivity
      exact mul_lt_mul_of_pos_left hεK_lt_εN hpos
    exact lt_trans h1 hKaufman_small_εN

  -- ========================================================================
  -- Step 3: Choose q and Δ = (1/2)^q
  -- ========================================================================
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log48_pos : 0 < Real.log 48 := Real.log_pos (by norm_num)
  have h_loglog2_neg : Real.log (Real.log 2) < 0 := by
    have h1 : 0 < Real.log 2 := h_log2_pos
    have h2 : Real.log 2 < 1 := by
      have h3 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      have h4 : Real.log 2 < Real.log (Real.exp 1) := Real.log_lt_log (by positivity) h3
      have h5 : Real.log (Real.exp 1) = 1 := by simp
      linarith
    exact Real.log_neg h1 h2

  have h_log_sqrt : ∀ (x : ℝ), 1 ≤ x → Real.log x ≤ 2 * Real.sqrt x := by
    intro x hx
    have h1 : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos h1
    have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      have h4 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
      have h5 : Real.log x = Real.log (Real.sqrt x ^ 2) := by rw [h4]
      rw [h5, Real.log_pow] <;> norm_num
    rw [h3]; linarith

  let Q_root : ℝ := 2 * Real.log 9 / ((ε_K - ε_Root) * Real.log 2)
  let Q_rho : ℝ := (4 * (Real.log 48 + 2) / (ε_Root * Real.log 2)) ^ 2
  let Q : ℝ := max Q_root Q_rho

  have hQ_pos : 0 < Q := by dsimp only [Q, Q_root, Q_rho] <;> positivity
  have h_exists_q : ∃ (q : ℕ), 0 < q ∧ (q : ℝ) ≥ Q := by
    rcases exists_nat_ge Q with ⟨q, hq⟩
    have hq_pos : 0 < q := by
      have h4 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le hQ_pos hq
      exact_mod_cast h4
    exact ⟨q, hq_pos, hq⟩

  rcases h_exists_q with ⟨q, hq_pos, hq_ge_Q⟩
  have hq_ge_root : (q : ℝ) ≥ Q_root := by
    have h : (q : ℝ) ≥ Q := hq_ge_Q
    exact le_trans (le_max_left _ _) h
  have hq_ge_rho : (q : ℝ) ≥ Q_rho := by
    have h : (q : ℝ) ≥ Q := hq_ge_Q
    exact le_trans (le_max_right _ _) h
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by
    have h : (q : ℝ) ≥ Q := hq_ge_Q
    have hq_pos' : 0 < q := by exact_mod_cast (lt_of_lt_of_le hQ_pos h)
    have h1 : 1 ≤ q := Nat.succ_le_iff.mpr hq_pos'
    exact_mod_cast h1

  let Δ : ℝ := (1 / 2 : ℝ) ^ q
  have hΔ_pos : 0 < Δ := by positivity
  have hΔ_lt_one : Δ < 1 := by
    have h2 : (1 / 2 : ℝ) ^ q < 1 := by
      have h3 : 0 < q := hq_pos
      have h4 : (1 / 2 : ℝ) < 1 := by norm_num
      have h5 : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have h6 : ∀ (n : ℕ), 0 < n → (1 / 2 : ℝ) ^ n < 1 := by
        intro n hn
        induction n with
        | zero => contradiction
        | succ n ih =>
          cases n with
          | zero => norm_num
          | succ n => simp [pow_succ] at * <;> nlinarith
      exact h6 q h3
    exact h2
  have hΔ_le_half : Δ ≤ 1 / 2 := by
    have h1 : 1 ≤ q := by linarith
    have h2 : (1 / 2 : ℝ) ^ q ≤ (1 / 2 : ℝ) ^ 1 := by
      apply pow_le_pow_of_le_one <;> norm_num <;> linarith
    have h3 : (1 / 2 : ℝ) ^ 1 = 1 / 2 := by norm_num
    rw [h3] at h2; exact h2
  have hΔ_eq : Δ = (1 / 2 : ℝ) ^ q := by rfl
  have hΔ_dyadic_scales : Δ ∈ dyadicScales := by
    refine' ⟨q, _⟩
    have h1 : Δ = (2 : ℝ)^ (-(q : ℤ)) := by
      dsimp only [Δ]
      have h2 : (1 / 2 : ℝ)^q = (2 : ℝ)^ (-(q : ℤ)) := by
        simp [zpow_neg, zpow_ofNat] <;> ring
      exact h2
    exact h1
  have hΔ_dyadic_kaufman : ∃ (n : ℕ), 0 < n ∧ (1 : ℝ) = (n : ℝ) * Δ := by
    refine' ⟨2 ^ q, by positivity, _⟩
    have h_eq : ((2 ^ q : ℕ) : ℝ) * Δ = 1 := by
      have h4 : ((2 ^ q : ℕ) : ℝ) = (2 : ℝ) ^ q := by norm_cast
      rw [h4]
      have h5 : (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ q = 1 := by
        have h6 : (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ q = ((2 : ℝ) * (1 / 2 : ℝ)) ^ q := by rw [←mul_pow]
        rw [h6]; norm_num
      exact h5
    exact h_eq.symm

  have h_log1Δ : Real.log (1 / Δ) = (q : ℝ) * Real.log 2 := by
    have h1 : 1 / Δ = (2 : ℝ) ^ q := by
      have h2 : Δ = (1 / 2 : ℝ) ^ q := rfl
      rw [h2]
      have h3 : (1 / 2 : ℝ) ^ q = 1 / (2 : ℝ) ^ q := by
        rw [←one_div_pow] <;> norm_num
      rw [h3]
      field_simp
    rw [h1, Real.log_pow] <;> norm_num

  -- ========================================================================
  -- Step 4: Uniformization density bound ρ(Δ) ≤ ε_Root / 4
  -- ========================================================================
  let rho : ℝ := Real.log (48 * Real.log (1 / Δ)) / Real.log (1 / Δ)
  have h_rho_bound : rho ≤ ε_Root / 4 := by
    have hq_real_ge_one : 1 ≤ (q : ℝ) := hq_ge_one
    have h1 : Real.log (48 * (q : ℝ) * Real.log 2) < Real.log 48 + Real.log (q : ℝ) := by
      have h2 : 0 < Real.log 2 := h_log2_pos
      have h3 : Real.log (48 * (q : ℝ) * Real.log 2) =
          Real.log 48 + Real.log (q : ℝ) + Real.log (Real.log 2) := by
        have h4 : 0 < (q : ℝ) := by exact_mod_cast hq_pos
        have h31 : Real.log ((48 * (q : ℝ)) * Real.log 2) =
            Real.log (48 * (q : ℝ)) + Real.log (Real.log 2) :=
          Real.log_mul (by positivity) (by positivity)
        have h32 : Real.log (48 * (q : ℝ)) = Real.log 48 + Real.log (q : ℝ) :=
          Real.log_mul (by positivity) (by positivity)
        have h_eq : 48 * (q : ℝ) * Real.log 2 = (48 * (q : ℝ)) * Real.log 2 := by ring
        rw [h_eq, h31, h32] <;> ring
      rw [h3]
      linarith [h_loglog2_neg]
    have h4 : Real.log (q : ℝ) ≤ 2 * Real.sqrt (q : ℝ) := h_log_sqrt (q : ℝ) hq_real_ge_one
    have h5 : Real.log 48 + 2 * Real.sqrt (q : ℝ) ≤
        (Real.log 48 + 2) * Real.sqrt (q : ℝ) := by
      have h6 : 1 ≤ Real.sqrt (q : ℝ) := by
        have h7 : 1 ≤ (q : ℝ) := hq_real_ge_one
        have h8 : Real.sqrt (q : ℝ) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h7
        simpa using h8
      nlinarith [Real.log_pos (show (1 : ℝ) < 48 by norm_num)]
    have h6 : Real.log (48 * (q : ℝ) * Real.log 2) <
        (Real.log 48 + 2) * Real.sqrt (q : ℝ) := by linarith
    have h7 : Real.log (1 / Δ) = (q : ℝ) * Real.log 2 := h_log1Δ
    have h8 : Real.sqrt (q : ℝ) ≥ 4 * (Real.log 48 + 2) / (ε_Root * Real.log 2) := by
      have h9 : (q : ℝ) ≥ Q_rho := hq_ge_rho
      dsimp only [Q_rho] at h9
      have h10 : 0 < ε_Root * Real.log 2 := by positivity
      have h11 : Real.sqrt (q : ℝ) ≥ 4 * (Real.log 48 + 2) / (ε_Root * Real.log 2) := by
        calc Real.sqrt (q : ℝ)
          ≥ Real.sqrt ((4 * (Real.log 48 + 2) / (ε_Root * Real.log 2)) ^ 2) := by gcongr
        _ = 4 * (Real.log 48 + 2) / (ε_Root * Real.log 2) := by
          have h12 : 0 < 4 * (Real.log 48 + 2) / (ε_Root * Real.log 2) := by positivity
          rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_pos h12]
      exact h11
    have h_rho_eq : rho = Real.log (48 * (q : ℝ) * Real.log 2) / ((q : ℝ) * Real.log 2) := by
      dsimp only [rho]
      have h9 : 48 * Real.log (1 / Δ) = 48 * ((q : ℝ) * Real.log 2) := by rw [h_log1Δ] <;> ring
      rw [h9, h7] <;> ring_nf
    rw [h_rho_eq]
    have h13 : Real.log (48 * (q : ℝ) * Real.log 2) / ((q : ℝ) * Real.log 2) ≤
        (Real.log 48 + 2) * Real.sqrt (q : ℝ) / ((q : ℝ) * Real.log 2) := by gcongr
    have h14 : (Real.log 48 + 2) * Real.sqrt (q : ℝ) / ((q : ℝ) * Real.log 2) ≤ ε_Root / 4 := by
      have h15 : 0 < (q : ℝ) := by exact_mod_cast hq_pos
      have h16 : 0 < Real.log 2 := h_log2_pos
      have h17 : (Real.log 48 + 2) * Real.sqrt (q : ℝ) / ((q : ℝ) * Real.log 2) =
          (Real.log 48 + 2) / (Real.sqrt (q : ℝ) * Real.log 2) := by
        field_simp [h15.ne', h16.ne'] <;> nlinarith [Real.sq_sqrt (show 0 ≤ (q : ℝ) by linarith)]
      rw [h17]
      have h18 : (Real.log 48 + 2) / (Real.sqrt (q : ℝ) * Real.log 2) ≤ ε_Root / 4 := by
        calc (Real.log 48 + 2) / (Real.sqrt (q : ℝ) * Real.log 2)
          ≤ (Real.log 48 + 2) / ((4 * (Real.log 48 + 2) / (ε_Root * Real.log 2)) * Real.log 2) := by gcongr
        _ = ε_Root / 4 := by
          have h19 : 0 < Real.log 48 + 2 := by positivity
          field_simp [h19.ne', h16.ne'] <;> ring
      exact h18
    exact le_trans h13 h14

  -- ========================================================================
  -- Step 5: Root error bound
  -- ========================================================================
  have hεK_root : ε_Root + 2 * Real.log 9 / Real.log (1 / Δ) ≤ ε_K := by
    rw [h_log1Δ]
    have h_epsK_diff_pos : 0 < ε_K - ε_Root := by
      have h1 : ε_Root = ε_K / 2 := by
        dsimp only [ε_Root, ε_K]
        <;> field_simp [hB_K_pos.ne'] <;> ring
      rw [h1]
      linarith [hεK_pos]
    have h_log9_pos : 0 < Real.log 9 := Real.log_pos (by norm_num)
    have h_q_ge : (q : ℝ) ≥ 2 * Real.log 9 / ((ε_K - ε_Root) * Real.log 2) := by
      simpa [Q_root] using hq_ge_root
    have h_denom_pos : 0 < (ε_K - ε_Root) * Real.log 2 := by positivity
    have h_mul_pos : 0 < (q : ℝ) * Real.log 2 := by positivity
    have h9 : 2 * Real.log 9 ≤ (q : ℝ) * ((ε_K - ε_Root) * Real.log 2) := by
      have h10 : 2 * Real.log 9 =
          (2 * Real.log 9 / ((ε_K - ε_Root) * Real.log 2)) * ((ε_K - ε_Root) * Real.log 2) := by
        field_simp [h_denom_pos.ne'] <;> ring
      rw [h10]
      exact mul_le_mul_of_nonneg_right h_q_ge h_denom_pos.le
    have h11 : 2 * Real.log 9 ≤ (ε_K - ε_Root) * ((q : ℝ) * Real.log 2) := by
      have h12 : (q : ℝ) * ((ε_K - ε_Root) * Real.log 2) = (ε_K - ε_Root) * ((q : ℝ) * Real.log 2) := by ring
      rw [h12] at h9
      exact h9
    have h14 : 0 < (q : ℝ) * Real.log 2 := h_mul_pos
    have h15 : 2 * Real.log 9 / ((q : ℝ) * Real.log 2) ≤ ((ε_K - ε_Root) * ((q : ℝ) * Real.log 2)) / ((q : ℝ) * Real.log 2) := by
      have hinv : 0 ≤ 1 / ((q : ℝ) * Real.log 2) := by positivity
      have h : 2 * Real.log 9 * (1 / ((q : ℝ) * Real.log 2)) ≤ ((ε_K - ε_Root) * ((q : ℝ) * Real.log 2)) * (1 / ((q : ℝ) * Real.log 2)) :=
        mul_le_mul_of_nonneg_right h11 hinv
      simpa [div_eq_mul_inv] using h
    have h16 : ((ε_K - ε_Root) * ((q : ℝ) * Real.log 2)) / ((q : ℝ) * Real.log 2) = ε_K - ε_Root := by
      field_simp [h14.ne'] <;> ring
    have h13 : 2 * Real.log 9 / ((q : ℝ) * Real.log 2) ≤ ε_K - ε_Root := by
      rw [h16] at h15
      exact h15
    linarith

  -- ========================================================================
  -- Step 6: Call multiscaleDecompKaufman
  -- ========================================================================
  have ht_le_two : t ≤ 2 := by linarith
  rcases multiscaleDecompKaufman
      hs hst ht_le_two hΔ_pos hΔ_lt_one hΔ_le_half
      (hε := hε_Root_pos) hεK_pos hεK_root hKaufman_small hΔ_dyadic_kaufman
    with ⟨τ, ε_bad, hτ_pos, hτ_le_eps, hε_bad_pos, hε_bad_bound, m0_root, H_root⟩

  have hτ_lt_one : τ < 1 := by
    have h1 : τ ≤ ε_Root := hτ_le_eps
    have h2 : ε_Root < 1 := by
      dsimp only [ε_Root, ε_K, ε_N, B_K]
      have h3 : ε_G ≤ (t - s) / 2 := by dsimp only [ε_G]; exact min_le_right _ _
      have h4 : η ≤ 1 := hη_le_one
      have h5 : B_K ≥ 3 := hB_K_ge3
      linarith
    linarith

  have hε_bad_lt_εN : ε_bad < ε_N := by
    have h1 : ε_bad ≤ B_K * ε_K := hε_bad_bound
    have h2 : B_K * ε_K = ε_N / 2 := by
      dsimp only [ε_K]
      field_simp [hB_K_pos.ne'] <;> ring
    rw [h2] at h1
    have h3 : ε_N / 2 < ε_N := by linarith [hεN_pos]
    exact lt_of_le_of_lt h1 h3

  have hε_bad_le_quarter_εG : ε_bad ≤ ε_G / 4 := by
    have h1 : ε_bad ≤ ε_N / 2 := by
      have h2 : ε_bad ≤ B_K * ε_K := hε_bad_bound
      have h3 : B_K * ε_K = ε_N / 2 := by
        dsimp only [ε_K]
        field_simp [hB_K_pos.ne'] <;> ring
      rw [h3] at h2; exact h2
    have h4 : ε_N ≤ ε_G / 100 := by
      dsimp only [ε_N]
      have h5 : η ≤ 1 := hη_le_one
      have h6 : ε_G * η ≤ ε_G := by
        have hη_le_one' : η ≤ 1 := hη_le_one
        have hεG_nonneg : 0 ≤ ε_G := hεG_pos.le
        have h61 : ε_G * η ≤ ε_G * (1 : ℝ) := mul_le_mul_of_nonneg_left hη_le_one' hεG_nonneg
        have h62 : ε_G * (1 : ℝ) = ε_G := by ring
        rw [h62] at h61
        exact h61
      have h7 : ε_G * η / 100 ≤ ε_G / 100 := by gcongr
      linarith
    linarith

  have hε_bad_lt_half_εG : ε_bad < ε_G / 2 := by
    have h1 : ε_bad ≤ ε_N / 2 := by
      have h2 : ε_bad ≤ B_K * ε_K := hε_bad_bound
      have h3 : B_K * ε_K = ε_N / 2 := by
        dsimp only [ε_K]
        field_simp [hB_K_pos.ne'] <;> ring
      rw [h3] at h2; exact h2
    have h4 : ε_N ≤ ε_G / 100 := by
      dsimp only [ε_N]
      have h5 : η ≤ 1 := hη_le_one
      have h6 : ε_G * η ≤ ε_G := by
        have hη_le_one' : η ≤ 1 := hη_le_one
        have hεG_nonneg : 0 ≤ ε_G := hεG_pos.le
        have h61 : ε_G * η ≤ ε_G * (1 : ℝ) := mul_le_mul_of_nonneg_left hη_le_one' hεG_nonneg
        have h62 : ε_G * (1 : ℝ) = ε_G := by ring
        rw [h62] at h61
        exact h61
      have h7 : ε_G * η / 100 ≤ ε_G / 100 := by gcongr
      linarith
    linarith

  have h_exp_condition : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc :=
    hsmall ε_G η hεG_pos hεG_le hη_pos hη_le

  -- ========================================================================
  -- Step 7: Call step5_source_faithful_v8
  -- ========================================================================
  -- Convert H_root: combined conjuncts → separated quantifiers
  have H_root' : ∀ (m : ℕ), m ≥ m0_root → ∀ (P : Set EuclideanPlane) (N : ℕ → ℕ),
      P ⊆ Metric.closedBall 0 1 →
      IsDyadicUniform P m Δ N →
      IsDeltaSSet (Δ ^ m) t (Real.rpow (Δ ^ m) (-ε_Root)) P →
      ∃ (n : ℕ) (i : ℕ → ℕ) (t_j : ℕ → ℝ)
        (S B : Finset (Fin n)),
        (i 0 = 0) ∧ (i n = m) ∧
        (∀ j < n, i j < i (j + 1)) ∧
        (∀ j : Fin n, t_j j.val ∈ Set.Icc s 2) ∧
        (S ∪ B = Finset.univ) ∧ (Disjoint S B) ∧
        (∀ j : Fin n, j ∈ S →
          (Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)) ≥ Real.rpow (Δ ^ m) (-τ)) ∧
        (∏ j ∈ B, ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)))) ≤ Real.rpow (Δ ^ m) (-ε_bad) ∧
        (∀ j : Fin n, j ∈ S →
          MultiscaleDecomposition.IsSetBetweenScales P
            (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
            ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)) ∧
        (∀ j : Fin n, j ∈ S → t_j j.val > s →
          MultiscaleDecomposition.IsRegularBetweenScales P
            (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
            ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)
            ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)) ∧
        (∏ j ∈ S, Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) (t_j j.val) ≥
          Real.rpow (Δ ^ m) (ε_bad - t)) ∧
        (∀ j : Fin n, j ∈ B → ∀ k : Fin n, k.val = j.val + 1 → k ∉ B) := by
    intro m hm P N hP_bdd hP_dyadic hP_sset
    rcases H_root m hm P N hP_bdd hP_dyadic hP_sset
      with ⟨n, i, t_j, S, B, h1, h2, h3, h4, h5, h6, h7, h8_prod, h9_bundled, h10_prod, h11_disjoint⟩
    have h8_set : ∀ (j : Fin n), j ∈ S →
        MultiscaleDecomposition.IsSetBetweenScales P
          (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
          ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad) := by
      intro j hj; exact (h9_bundled j hj).1
    have h8_reg : ∀ (j : Fin n), j ∈ S → t_j j.val > s →
        MultiscaleDecomposition.IsRegularBetweenScales P
          (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
          ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)
          ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad) := by
      intro j hj; exact (h9_bundled j hj).2
    exact ⟨n, i, t_j, S, B, h1, h2, h3, h4, h5, h6, h7, h8_prod, h8_set, h8_reg, h10_prod, h11_disjoint⟩

  rcases step5_source_faithful_v8
      s t τ ε_G η ε_N ε_inc ε_Root ε_bad
      hs hs1 hst ht2
      hτ_pos hτ_lt_one
      hεG_pos hη_pos hεN_pos hε_inc_pos hε_bad_pos hε_Root_pos
      hεG_le_one hη_le_one hεN_le_εG hεG_small h_exp_condition
      ε_section9 ε_target
      hε_section9_pos hε_target_pos hε_target_lt_section9
      K hK_ge1 h_uniform
      ε_G0 η0 hεG0_pos hη0_pos hεG_le hη_le
      H_main
      B_K hB_K_ge3 hε_Root_eq hε_bad_lt_εN hε_bad_le_quarter_εG hε_bad_lt_half_εG
      hεN_eq hε_section9_le
      Δ q hq_pos hΔ_pos hΔ_lt_one hΔ_eq hΔ_dyadic_scales
      h_rho_bound
      K_plane K_affine hK_plane_ge1 hK_affine_ge1
      reserved_budget hbudget_pos
      m0_root H_root'
    with ⟨ε_input, v8δ₀, hε_input_pos, hε_input_lt_Root, hv8δ₀_pos, h_v8_main⟩

  -- ========================================================================
  -- Step 8: Weaken exponents and return
  -- ========================================================================
  let ε_final : ℝ := min ε_input ε_target
  have hε_final_pos : 0 < ε_final := by
    dsimp only [ε_final]
    exact lt_min hε_input_pos hε_target_pos

  -- Choose outer δ₀ = min(v8δ₀, Δ, 1/2) so δ ≤ δ₀ implies δ ≤ v8δ₀, δ ≤ Δ, δ < 1
  let outer_δ₀ : ℝ := min v8δ₀ (min Δ (1 / 2))
  have houter_δ₀_pos : 0 < outer_δ₀ := by positivity

  refine' ⟨ε_final, hε_final_pos, outer_δ₀, houter_δ₀_pos, _⟩

  intro δ hδ_pos hδ_le P hP_bdd hP_sset_final T Tp hTp_sub hTp_sset_final hTp_near

  have hδ_le_v8δ₀ : δ ≤ v8δ₀ := by
    have h1 : δ ≤ outer_δ₀ := hδ_le
    have h2 : outer_δ₀ ≤ v8δ₀ := min_le_left _ _
    exact le_trans h1 h2

  have hδ_le_Δ : δ ≤ Δ := by
    have h1 : δ ≤ outer_δ₀ := hδ_le
    have h2 : outer_δ₀ ≤ min Δ (1 / 2) := min_le_right _ _
    have h3 : min Δ (1 / 2) ≤ Δ := min_le_left _ _
    exact le_trans h1 (le_trans h2 h3)

  have hδ_lt_one : δ < 1 := by
    have h1 : δ ≤ outer_δ₀ := hδ_le
    have h2 : outer_δ₀ ≤ min Δ (1 / 2) := min_le_right _ _
    have h3 : min Δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have h4 : δ ≤ 1 / 2 := le_trans h1 (le_trans h2 h3)
    linarith

  -- Weaken source S-sets from ε_final to ε_input
  have hε_final_le_input : ε_final ≤ ε_input := by
    dsimp only [ε_final]
    exact min_le_left _ _

  have h_constant_le_P : Real.rpow δ (-ε_final) ≤ Real.rpow δ (-ε_input) := by
    have h1 : -ε_input ≤ -ε_final := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h1

  have hP_sset : IsDeltaSSet δ t (Real.rpow δ (-ε_input)) P :=
    LemmaE.IsDeltaSSet.weaken_constant hP_sset_final h_constant_le_P

  have h_constant_le_Tp : Real.rpow δ (-ε_final) ≤ Real.rpow δ (-ε_input) := h_constant_le_P

  have hTp_sset : ∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_input)) (Tp p hp) := by
    intro p hp
    exact LemmaE.IsDeltaSSet.weaken_constant (hTp_sset_final p hp) h_constant_le_Tp

  -- Apply v8 main theorem
  have h_main_result := h_v8_main δ hδ_pos hδ_lt_one hδ_le_Δ P hP_bdd hP_sset
    T Tp hTp_sub hTp_sset hTp_near hδ_le_v8δ₀

  -- The conclusion is at min ε_input ε_target = ε_final
  have h_final_eq : min ε_input ε_target = ε_final := by
    dsimp only [ε_final] <;> rfl
  rw [h_final_eq] at h_main_result
  exact h_main_result

end DirecretisedFurstenbergEstimate.Section9Assembly
