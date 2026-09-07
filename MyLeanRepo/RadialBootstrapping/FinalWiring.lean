module

/-
  FinalWiring.lean

  Draft of radial_bootstrapping_measure_thin_tubes theorem.

  Restructured version:
    1. uniform_furstenberg → ε_F, δ_star
    2. Choose τ = min(ε/100, β*ε/28, ε_F*ε/100) based on ε_F
    3. good_params_exist_with_tau → M + inner conclusion
    4. Inside ∀σ: call inner conclusion → r2, N + all scale conditions
    5. Define r0 = chooseR0 K τ r2 (r2 from inner conclusion, NOT chooseR2)
    6. Propagate r2 conditions to r ≤ r0 via monotonicity
    7. bootstrapping_one_direction_G × 2 (needs updated signature accepting r2)

  NOTE: bootstrapping_one_direction_G currently hardcodes chooseR2 and requires
  hεF_gt_σ + h_singleton_C_bound_r0. These are being removed in the signature
  update. Placeholder sorrys mark the integration points.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.HasMeasureThinTubes
public import MyLeanRepo.RadialBootstrapping.UniformFurstenberg
public import MyLeanRepo.RadialBootstrapping.ParameterSelectionFinal
public import MyLeanRepo.RadialBootstrapping.BootstrappingOneDirection
public import MyLeanRepo.RadialBootstrapping.ConcentratedParameterSelection
public import MyLeanRepo.RadialBootstrapping.FurstenbergCaller
public import MyLeanRepo.RadialBootstrapping.CXBound
public import MyLeanRepo.RadialBootstrapping.HMDelta
public import MyLeanRepo.RadialBootstrapping.SmallR2Refinement
public import MyLeanRepo.RadialBootstrapping.ThresholdAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

noncomputable section

namespace RadialBootstrapping

/-- The inner conclusion type of the radial bootstrapping theorem. -/
def BootstrappingConclusion (β ε τ M : ℝ) : Prop :=
  ∀ (σ c K C : ℝ) (ν₁ ν₂ : ProbabilityMeasure Point),
    (ν₁ : Measure Point).support ⊆ closedBall 0 1 →
    (ν₂ : Measure Point).support ⊆ closedBall 0 1 →
    σ ∈ Set.Icc β (1 - ε) →
    c ∈ Set.Ioo (0 : ℝ) (1 / 10) →
    1 ≤ K →
    1 ≤ C →
    (1 : ℝ) / 2 ≤ sInf {d : ℝ |
      ∃ x ∈ (ν₁ : Measure Point).support,
        ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d} →
    (∀ (x : Point) (r : ℝ), 0 < r → ν₁ (ball x r) ≤ Real.toNNReal (C * r)) →
    (∀ (x : Point) (r : ℝ), 0 < r → ν₂ (ball x r) ≤ Real.toNNReal (C * r)) →
    HasMeasureThinTubes σ K c ν₁ ν₂ →
    HasMeasureThinTubes σ K c ν₂ ν₁ →
    HasMeasureThinTubes (σ + τ) (Real.rpow (max K (C ^ 2 * M / c)) M) (3 * c) ν₁ ν₂ ∧
    HasMeasureThinTubes (σ + τ) (Real.rpow (max K (C ^ 2 * M / c)) M) (3 * c) ν₂ ν₁

/-- Helper: construct Q and prove all threshold bounds needed for hB_large. -/
lemma construct_Q_and_bounds
    (Q_min τ M c C K : ℝ) (hτ : 0 < τ) (hτ_lt_one : τ < 1)
    (hM_gt400 : M > 400 / τ^2) (hc : c ∈ Set.Ioo (0 : ℝ) (1 / 10))
    (hC : 1 ≤ C) (hK : 1 ≤ K) (hQ_min_pos : 0 < Q_min)
    (hτ2_Q : τ^2 ≤ 4000 / Q_min) :
    ∃ (Q : ℝ), Q = max K (C^2 * M / c) ∧ Q > 4000 / τ^2 ∧ Q ≥ Q_min ∧ K ≤ Q ∧ C ≤ Q := by
  let Q : ℝ := max K (C^2 * M / c)
  have hM_pos : 0 < M := by
    have h : 0 < 400 / τ^2 := by positivity
    linarith [hM_gt400]
  have hc_pos : 0 < c := hc.1
  have hC2 : C^2 ≥ 1 := by
    have h : C ≥ 1 := hC
    calc C^2 ≥ 1^2 := by gcongr
      _ = 1 := by norm_num
  have h_inv_c_gt10 : 1 / c > 10 := by
    have h6 : c < 1 / 10 := hc.2
    have h7 : 0 < c := hc_pos
    have h8 : 1 / c > 1 / (1 / 10) := by gcongr
    have h9 : 1 / (1 / 10 : ℝ) = 10 := by norm_num
    rw [h9] at h8; exact h8
  have hM_div_c_gt : M / c > 4000 / τ^2 := by
    have h9 : M / c = (1 / c) * M := by ring
    rw [h9]
    have h10 : (1 / c) * M > (1 / c) * (400 / τ^2) := by gcongr
    have h11 : (1 / c) * (400 / τ^2) > 10 * (400 / τ^2) := by gcongr
    have h12 : 10 * (400 / τ^2) = 4000 / τ^2 := by ring
    linarith
  have h3 : C^2 * M / c > 4000 / τ^2 := by
    have h5 : C^2 * M / c ≥ M / c := by
      have h6 : C^2 ≥ 1 := hC2
      have h7 : 0 < M / c := by positivity
      have h8 : C^2 * (M / c) ≥ 1 * (M / c) := by gcongr
      have h9 : C^2 * M / c = C^2 * (M / c) := by ring
      rw [h9]; simpa using h8
    calc C^2 * M / c ≥ M / c := h5
      _ > 4000 / τ^2 := hM_div_c_gt
  have h1 : Q ≥ C^2 * M / c := le_max_right _ _
  have hQ_large : Q > 4000 / τ^2 := by
    calc Q ≥ C^2 * M / c := h1
      _ > 4000 / τ^2 := h3
  have h7 : 4000 / τ^2 ≥ Q_min := by
    have h8 : 0 < τ^2 := by positivity
    have h9 : 0 < Q_min := hQ_min_pos
    have h10 : τ^2 ≤ 4000 / Q_min := hτ2_Q
    have h11 : 4000 / τ^2 ≥ 4000 / (4000 / Q_min) := by gcongr
    have h12 : 4000 / (4000 / Q_min) = Q_min := by
      field_simp [h9.ne'] <;> ring
    rw [h12] at h11; exact h11
  have hQ_min_le : Q ≥ Q_min := h7.trans hQ_large.le
  have hK_le_Q : K ≤ Q := le_max_left _ _
  have hM1 : M > 1 := by
    have h : τ^2 < 1 := by
      have h2 : τ < 1 := hτ_lt_one
      have h3 : 0 ≤ τ := by linarith
      nlinarith
    have h2 : 400 / τ^2 > 400 := by
      have h3 : τ^2 < 1 := h
      have h4 : 0 < τ^2 := by positivity
      calc 400 / τ^2 > 400 / 1 := by gcongr
        _ = 400 := by ring
    linarith [hM_gt400]
  have h_inv_c1 : 1 / c > 1 := by
    have h7 : c < 1 := by linarith [hc.2]
    have h8 : 0 < c := hc_pos
    have h9 : 1 / c > 1 / 1 := by gcongr
    simpa using h9
  have h10 : C^2 * M / c ≥ C := by
    have h11 : C^2 ≥ C := by
      have h12 : C ≥ 1 := hC
      nlinarith
    have h13 : M / c ≥ 1 := by
      have h14 : M > 1 := hM1
      have h15 : 1 / c > 1 := h_inv_c1
      have h16 : M / c = M * (1 / c) := by ring
      rw [h16]
      have h17 : M * (1 / c) > 1 * 1 := by gcongr
      linarith
    have h18 : C^2 * M / c = C^2 * (M / c) := by ring
    rw [h18]
    have h19 : C^2 * (M / c) ≥ C * 1 := by gcongr <;> linarith
    linarith
  have hC_le_Q : C ≤ Q := by
    have h1 : Q ≥ C^2 * M / c := le_max_right _ _
    exact h10.trans h1
  exact ⟨Q, rfl, hQ_large, hQ_min_le, hK_le_Q, hC_le_Q⟩

/-- Helper: prove hB_large: r_max > 4 / K'^(1/(σ+τ)). -/
lemma prove_hB_large
    (c Q M σ τ ε_F κ C K K' : ℝ) (D_T D_X : ℕ)
    (r_conc r_ext r_CB r_max : ℝ)
    (hQ_large : Q > 4000 / τ^2) (hM_large : M > 400 / τ^2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1) (hτ_small : τ < 1 / 14)
    (hστ_pos : 0 < σ + τ) (hστ_lt_two : σ + τ < 2)
    (hσ_pos : 0 < σ) (hσ_lt_one : σ < 1)
    (hτ_very_small : τ < (1 - σ) / 14)
    (hεF_large : ε_F > 8 * τ + 3 * κ)
    (hκ_nonneg : 0 ≤ κ) (hκ_lt_one : κ < 1)
    (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hK_le_Q : K ≤ Q) (hC_le_Q : C ≤ Q)
    (hDT_pos : 0 < D_T) (hDX_pos : 0 < D_X)
    (hDT_le_Q : (D_T : ℝ) ≤ Q) (hDX_le_Q : (D_X : ℝ) ≤ Q)
    (hQ_huge : Q ≥ (2 : ℝ)^(ε_F + 2))
    (hK'_def : K' = Real.rpow (max K (C ^ 2 * M / c)) M)
    (hQ_def : Q = max K (C ^ 2 * M / c))
    (hr_conc_eq : r_conc = ConcentratedParam.concentrated_r_conc σ τ C K κ)
    (hr_ext_eq : r_ext = c_x_r_ext τ ε_F C D_X)
    (hr_CB_eq : r_CB = Real.rpow (Real.rpow (2 : ℝ) (-ε_F) /
        (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7)) (1 / (ε_F - κ - 5 * τ)))
    (hr_max_eq : r_max = min r_CB (min r_conc (min r_ext (Real.rpow K (-(1 / τ)) / 2)))) :
    r_max > 4 / K'^(1 / (σ + τ)) := by
  have hr_max_eq2 : r_max = min (Real.rpow (Real.rpow (2 : ℝ) (-ε_F) /
        (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7)) (1 / (ε_F - κ - 5 * τ)))
      (min (ConcentratedParam.concentrated_r_conc σ τ C K κ)
        (min (c_x_r_ext τ ε_F C D_X) (Real.rpow K (-(1 / τ)) / 2))) := by
    rw [hr_max_eq, hr_CB_eq, hr_conc_eq, hr_ext_eq]
  have h1 : min (Real.rpow (Real.rpow (2 : ℝ) (-ε_F) /
        (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7)) (1 / (ε_F - κ - 5 * τ)))
      (min (ConcentratedParam.concentrated_r_conc σ τ C K κ)
        (min (c_x_r_ext τ ε_F C D_X) (Real.rpow K (-(1 / τ)) / 2))) >
      8 / Real.rpow Q (M / (σ + τ)) :=
    hB_large_assembled Q M σ τ ε_F κ C K D_T D_X
      hQ_large hM_large hτ_pos hτ_lt_one hτ_small hστ_pos hστ_lt_two
      hσ_pos hσ_lt_one hτ_very_small hεF_large hκ_nonneg hκ_lt_one
      hC hK hK_le_Q hC_le_Q hDT_pos hDX_pos hDT_le_Q hDX_le_Q hQ_huge
  have h4 : r_max > 8 / Real.rpow Q (M / (σ + τ)) := by
    rw [hr_max_eq2]; exact h1
  have hQ_pos : 0 < Q := by
    have h2 : 0 < 4000 / τ^2 := by positivity
    exact lt_trans h2 hQ_large
  have h_rpow_pos : 0 < Real.rpow Q (M / (σ + τ)) := Real.rpow_pos_of_pos hQ_pos _
  have h5 : (8 : ℝ) / Real.rpow Q (M / (σ + τ)) > 4 / Real.rpow Q (M / (σ + τ)) := by
    have h6 : (0 : ℝ) < Real.rpow Q (M / (σ + τ)) := h_rpow_pos
    have h7 : (8 : ℝ) / Real.rpow Q (M / (σ + τ)) = 2 * (4 / Real.rpow Q (M / (σ + τ))) := by
      field_simp [h6.ne'] <;> ring
    rw [h7]
    have h8 : 0 < 4 / Real.rpow Q (M / (σ + τ)) := by positivity
    linarith
  have h4' : r_max > 4 / Real.rpow Q (M / (σ + τ)) := lt_trans h5 h4
  have h2 : Real.rpow K' (1 / (σ + τ)) = Real.rpow Q (M / (σ + τ)) := by
    rw [hK'_def, hQ_def]
    have h3 : Real.rpow (Real.rpow (max K (C ^ 2 * M / c)) M) (1 / (σ + τ)) =
        Real.rpow (max K (C ^ 2 * M / c)) (M * (1 / (σ + τ))) := by
      have h4 := Real.rpow_mul (show 0 ≤ max K (C ^ 2 * M / c) from by positivity) M (1 / (σ + τ))
      exact h4.symm
    have h5 : M * (1 / (σ + τ)) = M / (σ + τ) := by ring
    rw [h3, h5]
  have h9 : (4 : ℝ) / K'^(1 / (σ + τ)) = 4 / Real.rpow K' (1 / (σ + τ)) := by rfl
  rw [h9, h2]
  exact h4'

/-- Main case of radial bootstrapping: β < 1 - ε. -/
lemma radial_bootstrapping_main_case (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε)
    (hβ_lt : β < 1 - ε) :
    ∃ (τ : ℝ), 0 < τ ∧ ∃ (M : ℝ), 1 ≤ M ∧ BootstrappingConclusion β ε τ M := by

  -- Step 1: Uniform Furstenberg estimate
  rcases uniform_furstenberg β ε hβ hε hβ_lt with ⟨ε_F, δ_star, hεF_pos, hδ_star_pos, hF_uniform⟩

  -- Step 1b: Define constants needed for τ bound
  let D_X_const : ℕ := Point_exists_doubling.choose
  let D_T_const : ℕ := Line2_exists_doubling.choose
  let δ₀ : ℝ := min δ_star 1
  have hδ0_pos : 0 < δ₀ := by positivity
  have hδ0_le_one : δ₀ ≤ 1 := by exact min_le_right _ _
  have hD_X_const_pos : 0 < D_X_const := Point_exists_doubling.choose_spec.1
  have hD_X_const_ge_one : 1 ≤ D_X_const := by exact_mod_cast hD_X_const_pos
  have hD_T_const_pos : 0 < D_T_const := Line2_exists_doubling.choose_spec.1

  -- Bound for hM_delta: ensure M*log(M) dominates lowerBound_M
  -- Added D_T term so τ is small enough for C_B threshold bounds
  let C_total : ℝ := 2754 + 2 * Real.log (1 / δ₀) + 2 * Real.log (100 * (D_X_const : ℝ))
      + 30 * Real.log ((D_T_const : ℝ) + 1)
  let τ_max_delta : ℝ := Real.sqrt (200 * Real.exp (-C_total / 400))
  have hτ_max_delta_pos : 0 < τ_max_delta := by positivity

  -- Bound for B component thresholds: ensure Q ≥ 2^(ε_F+2), D_T, D_X
  let Q_min : ℝ := max ((2 : ℝ)^(ε_F + 2)) (max ((D_T_const : ℝ)) ((D_X_const : ℝ)))
  let τ_max_Q : ℝ := Real.sqrt (4000 / Q_min)
  have hQ_min_pos : 0 < Q_min := by positivity
  have hτ_max_Q_pos : 0 < τ_max_Q := by positivity

  -- Step 2: Choose τ based on ε_F to satisfy all smallness conditions
  let τ : ℝ := min (ε / 100) (min (β * ε / 28) (min (ε_F * ε / 100) (min τ_max_delta τ_max_Q)))
  have hτ : 0 < τ := by
    dsimp only [τ]
    have h1 : 0 < ε / 100 := by positivity
    have h2 : 0 < β * ε / 28 := by positivity
    have h3 : 0 < ε_F * ε / 100 := by positivity
    positivity

  have hτ_lt_01 : τ < 1 / 100 := by
    dsimp only [τ]
    have h : τ ≤ ε / 100 := min_le_left _ _
    have h' : ε / 100 < 1 / 100 := by
      have hε_lt_one : ε < 1 := by linarith [hβ_lt, hβ]
      linarith
    linarith

  have hτ_le_eps100 : τ ≤ ε / 100 := min_le_left _ _

  have hτ_small_all : ∀ σ ∈ Set.Icc β (1 - ε), τ < (1 - σ) / 14 := by
    intro σ hσ
    have h1 : 1 - σ ≥ ε := by linarith [hσ.2]
    have h2 : τ ≤ ε / 100 := hτ_le_eps100
    calc τ ≤ ε / 100 := h2
      _ < ε / 14 := by gcongr <;> norm_num
      _ ≤ (1 - σ) / 14 := by gcongr

  have hκ_le_014_all : ∀ σ ∈ Set.Icc β (1 - ε), 14 * τ / (1 - σ) ≤ 14 / 100 := by
    intro σ hσ
    have h1 : 1 - σ ≥ ε := by linarith [hσ.2]
    have h2 : 14 * τ / (1 - σ) ≤ 14 * τ / ε := by gcongr
    have h3 : τ ≤ ε / 100 := hτ_le_eps100
    have h4 : 14 * τ / ε ≤ 14 / 100 := by
      calc 14 * τ / ε ≤ 14 * (ε / 100) / ε := by gcongr
        _ = 14 / 100 := by
          field_simp [hε.ne'] <;> ring
    linarith

  -- Step 3: good_params_exist_with_tau → M
  rcases good_params_exist_with_tau β ε τ hβ hε hτ hτ_lt_01 hτ_le_eps100 hτ_small_all with
    ⟨M, hM, hM_gt2s, hM_gt400, h_inner⟩

  refine' ⟨τ, hτ, M, hM, _⟩
  dsimp only [BootstrappingConclusion]
  intro σ c K C ν₁ ν₂ h_supp1 h_supp2 hσ hc hK hC h_dist hν₁_growth hν₂_growth h_thin12 h_thin21

  -- Step 4: Define constants
  let C_X_const : ℝ := 100
  let D_X : ℕ := Point_exists_doubling.choose
  let D_T : ℕ := D_T_const
  let C₁ : ℝ := 1
  let κ : ℝ := 14 * τ / (1 - σ)
  let K' : ℝ := Real.rpow (max K (C ^ 2 * M / c)) M

  have hD_X_pos : 0 < D_X := Point_exists_doubling.choose_spec.1
  have hD_T_pos : 0 < D_T := Line2_exists_doubling.choose_spec.1
  have h1_minusσ_pos : 0 < 1 - σ := by linarith [hσ.2, hε]
  have hσ_pos : 0 < σ := by linarith [hσ.1, hβ]
  have hσ_lt_one : σ < 1 := by linarith [hσ.2, hε]
  have hκ_pos : 0 < κ := by dsimp only [κ]; positivity
  have hκ_lt_one : κ < 1 := by
    dsimp only [κ]
    have h : τ < (1 - σ) / 14 := hτ_small_all σ hσ
    have h' : 14 * τ < 1 - σ := by linarith
    have h'' : 14 * τ / (1 - σ) < 1 := by
      calc 14 * τ / (1 - σ)
        < (1 - σ) / (1 - σ) := by gcongr
        _ = 1 := by field_simp [h1_minusσ_pos.ne'] <;> ring
    exact h''
  have hK'_def : K' = Real.rpow (max K (C ^ 2 * M / c)) M := by rfl

  -- Step 5: Prove hεF_large3 and hεF_large from τ selection
  have h_eps_lt_one : ε < 1 := by linarith [hβ_lt, hβ]
  have hτ_le_epsF : τ ≤ ε_F * ε / 100 := by
    dsimp only [τ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hκ_le : κ ≤ 14 * τ / ε := by
    dsimp only [κ]
    have h1 : 1 - σ ≥ ε := by linarith [hσ.2]
    gcongr

  have hεF_large3 : 8 * τ + 3 * κ < ε_F := by
    have h4 : 8 * τ + 3 * κ ≤ τ * (8 + 42 / ε) := by
      calc 8 * τ + 3 * κ
        ≤ 8 * τ + 3 * (14 * τ / ε) := by gcongr
        _ = τ * (8 + 42 / ε) := by ring
    have h6 : τ * (8 + 42 / ε) ≤ (ε_F * ε / 100) * (8 + 42 / ε) := by gcongr
    have h7 : (ε_F * ε / 100) * (8 + 42 / ε) = ε_F * (8 * ε + 42) / 100 := by
      field_simp [hε.ne'] <;> ring
    rw [h7] at h6
    have h8 : ε_F * (8 * ε + 42) / 100 < ε_F := by
      have h9 : 8 * ε + 42 < 100 := by nlinarith
      nlinarith [hεF_pos]
    linarith

  have hεF_large : 8 * τ + 4 * κ < ε_F := by
    have h4 : 8 * τ + 4 * κ ≤ τ * (8 + 56 / ε) := by
      calc 8 * τ + 4 * κ
        ≤ 8 * τ + 4 * (14 * τ / ε) := by gcongr
        _ = τ * (8 + 56 / ε) := by ring
    have h6 : τ * (8 + 56 / ε) ≤ (ε_F * ε / 100) * (8 + 56 / ε) := by gcongr
    have h7 : (ε_F * ε / 100) * (8 + 56 / ε) = ε_F * (8 * ε + 56) / 100 := by
      field_simp [hε.ne'] <;> ring
    rw [h7] at h6
    have h8 : ε_F * (8 * ε + 56) / 100 < ε_F := by
      have h9 : 8 * ε + 56 < 100 := by nlinarith
      nlinarith [hεF_pos]
    linarith

  -- Step 6: Prove hτ_small2 from τ selection
  have hτ_small2 : τ < σ * (1 - σ) / (11 + 3 * σ) := by
    have h1 : τ ≤ β * ε / 28 := by
      dsimp only [τ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have h2 : σ ≥ β := hσ.1
    have h3 : 1 - σ ≥ ε := by linarith [hσ.2]
    have h4 : σ * (1 - σ) ≥ β * ε := by nlinarith
    have h5 : 0 < 11 + 3 * σ := by linarith
    have h5' : 11 + 3 * σ < 14 := by linarith
    have h_pos : 0 < β * ε := by positivity
    have h61 : (β * ε) / (11 + 3 * σ) > (β * ε) / 14 := by
      have h_diff : 0 < 14 - (11 + 3 * σ) := by linarith
      have h : (β * ε) / (11 + 3 * σ) - (β * ε) / 14 =
          (β * ε) * (14 - (11 + 3 * σ)) / ((11 + 3 * σ) * 14) := by
        field_simp [h5.ne'] <;> ring
      have h_pos2 : 0 < (β * ε) * (14 - (11 + 3 * σ)) / ((11 + 3 * σ) * 14) := by
        apply div_pos
        · positivity
        · positivity
      linarith [h, h_pos2]
    have h62 : σ * (1 - σ) / (11 + 3 * σ) ≥ (β * ε) / (11 + 3 * σ) := by
      gcongr
      <;> linarith
    have h6 : σ * (1 - σ) / (11 + 3 * σ) > β * ε / 14 := by
      calc σ * (1 - σ) / (11 + 3 * σ)
        ≥ (β * ε) / (11 + 3 * σ) := h62
      _ > (β * ε) / 14 := h61
    calc τ ≤ β * ε / 28 := h1
      _ < β * ε / 14 := by gcongr <;> norm_num
      _ < σ * (1 - σ) / (11 + 3 * σ) := h6

  -- Step 7: Furstenberg estimate
  have hF_estimate : ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ δ_star →
      ∀ (X : Set Point) (T : Point → Set Line2),
        X.Nonempty → X ⊆ closedBall 0 1 →
        IsDeltaSet δ 1 (Real.rpow δ (-ε_F)) hδ (by norm_num) (Real.rpow_nonneg hδ.le _) X →
        (∀ x ∈ X, (T x).Nonempty ∧
          IsDeltaSet δ σ (Real.rpow δ (-ε_F)) hδ (by linarith [hσ.1, hβ]) (Real.rpow_nonneg hδ.le _) (T x) ∧
          ∀ ℓ ∈ T x, x ∈ tube δ ℓ) →
        Set.Finite (⋃ x ∈ X, T x) →
        (⋃ x ∈ X, T x).ncard ≥ Nat.ceil (Real.rpow δ (-2 * σ - ε_F)) :=
    hF_uniform σ hσ


  -- Step 8: Prove hM_delta via HMDelta.hM_delta_lemma
  have hC_total_ge : C_total ≥ 2754 + 2 * Real.log (1 / δ₀) + 2 * Real.log (100 * (D_X : ℝ)) := by
    dsimp only [C_total, D_X_const, D_X]
    have h1 : 0 ≤ 30 * Real.log ((D_T_const : ℝ) + 1) := by
      have h2 : (D_T_const : ℝ) + 1 ≥ 2 := by
        have h3 : (D_T_const : ℝ) ≥ 1 := by exact_mod_cast (Nat.succ_le_iff.mpr hD_T_const_pos)
        linarith
      have h3 : 0 ≤ Real.log ((D_T_const : ℝ) + 1) := Real.log_nonneg (by linarith)
      positivity
    linarith
  have hτ2_le : τ^2 ≤ 200 * Real.exp (-C_total / 400) := by
    have h1 : τ ≤ Real.sqrt (200 * Real.exp (-C_total / 400)) := by
      dsimp only [τ, τ_max_delta]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
    have h2 : 0 ≤ 200 * Real.exp (-C_total / 400) := by positivity
    have h3 : τ^2 ≤ (Real.sqrt (200 * Real.exp (-C_total / 400)))^2 := by nlinarith [hτ]
    have h4 : (Real.sqrt (200 * Real.exp (-C_total / 400)))^2 = 200 * Real.exp (-C_total / 400) := by
      rw [Real.sq_sqrt] <;> positivity
    rw [h4] at h3; exact h3
  have hC_total_pos : 0 < C_total := by
    dsimp only [C_total]
    have h1 : 0 ≤ Real.log (1 / δ₀) := by
      have h2 : 1 ≤ 1 / δ₀ := by field_simp [hδ0_pos.ne'] <;> linarith
      exact Real.log_nonneg h2
    have h3 : 0 ≤ Real.log (100 * (D_X_const : ℝ)) := by
      have h4 : 1 ≤ 100 * (D_X_const : ℝ) := by
        have h5 : (D_X_const : ℝ) ≥ 1 := by exact_mod_cast hD_X_const_ge_one
        nlinarith
      exact Real.log_nonneg h4
    have h6 : 0 ≤ 30 * Real.log ((D_T_const : ℝ) + 1) := by
      have h7 : (D_T_const : ℝ) + 1 ≥ 2 := by
        have h8 : (D_T_const : ℝ) ≥ 1 := by exact_mod_cast (Nat.succ_le_iff.mpr hD_T_const_pos)
        linarith
      have h8 : 0 ≤ Real.log ((D_T_const : ℝ) + 1) := Real.log_nonneg (by linarith)
      positivity
    linarith
  have hM_delta : M * Real.log M / ((σ + τ) * Real.log 2) >
      Real.log (8 / τ) / (τ * Real.log 2) +
      400 / (τ^2 * Real.log 2) +
      Real.log 390 / (τ * Real.log 2) + 8 +
      Real.log (1 / δ₀) / Real.log 2 +
      (2 * σ + ε_F + Real.log 80000 / Real.log 2) / (ε_F - 8 * τ - 3 * κ) +
      Real.log (100 * (D_X : ℝ)) / (ε_F * Real.log 2) :=
    hM_delta_lemma τ σ ε_F κ δ₀ C_total M D_X ε
      hτ hτ_lt_01 hσ_pos hσ_lt_one
      hεF_pos hεF_large3 hδ0_pos hδ0_le_one hD_X_pos
      hε h_eps_lt_one hτ_le_epsF hκ_le hτ_le_eps100 hσ.2
      hM_gt400 hτ2_le hC_total_pos hC_total_ge


  -- Apply hN_ok_holds_full with δ₀
  have hN_ok0 : lowerBound_M τ σ c C ε_F δ₀ (1 : ℝ) (D_X : ℝ) C_X_const (D_X : ℝ) + 3 <
      M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) :=
    hN_ok_holds_full τ σ c C M δ₀ ε_F C_X_const (D_X : ℝ)
      hτ hτ_lt_01 hσ_pos hσ_lt_one (hτ_small_all σ hσ) hc hC
      hδ0_pos hδ0_le_one hεF_pos hεF_large
      (by norm_num) (by exact_mod_cast hD_X_pos) (by norm_num) (by exact_mod_cast hD_X_pos)
      (hM_gt2s σ hσ) hM_gt400 hM_delta

  -- lowerBound_M is monotone in δ₀: smaller δ₀ gives larger bound.
  -- Since δ₀ ≤ δ_star, lowerBound_M(δ_star) ≤ lowerBound_M(δ₀)
  have hN_ok : lowerBound_M τ σ c C ε_F δ_star C₁ (D_T : ℝ) C_X_const (D_X : ℝ) + 3 <
      M * Real.log (C ^ 2 * M / c) / ((σ + τ) * Real.log 2) := by
    have h_monotone : lowerBound_M τ σ c C ε_F δ_star C₁ (D_T : ℝ) C_X_const (D_X : ℝ) ≤
        lowerBound_M τ σ c C ε_F δ₀ (1 : ℝ) (D_X : ℝ) C_X_const (D_X : ℝ) := by
      simp only [lowerBound_M]
      have h1 : δ₀ ≤ δ_star := min_le_left _ _
      have h2 : 0 < δ₀ := hδ0_pos
      have h3 : Real.log (1 / δ_star) ≤ Real.log (1 / δ₀) := by
        apply Real.log_le_log
        · positivity
        · gcongr
      gcongr
      <;> simp [h3] <;> ring
    linarith [hN_ok0, h_monotone]

  -- Step 9: Call inner conclusion to get r2, N and all conditions
  rcases h_inner σ c K C C₁ (D_T : ℝ) C_X_const (D_X : ℝ) ε_F δ_star
      hσ hc hK hC
      (by norm_num) (Nat.cast_pos.mpr hD_T_pos) (by norm_num) (Nat.cast_pos.mpr hD_X_pos)
      hεF_pos hδ_star_pos hεF_large hN_ok with
    ⟨r2, N, hr2_eq, h_geom_sum, hτ_small_r2, hK'_r0_large_r2, hK'_r0_lower_r2,
     h_r2_tau_le, h_r2_kappa_le_half, h_r2_1mkappa_le_sqrt34, h_r2_1mkappa_le_116,
     h_r2_log_le, h_20C_r2_tau, h_2r2_le_delta, h_scale_r2, h_C_X_D_X_r2⟩

  let r0 : ℝ := chooseR0 K τ r2 hK hτ
  have hr0_eq : r0 = chooseR0 K τ r2 hK hτ := by rfl
  have hr0_pos : 0 < r0 := by
    have h_r0_def : r0 = min (Real.rpow K (-(1 / τ))) r2 := by rfl
    rw [h_r0_def]
    have hK_pos : 0 < K := by linarith
    have h1 : 0 < Real.rpow K (-(1 / τ)) := Real.rpow_pos_of_pos hK_pos _
    have h2 : 0 < r2 := by
      rw [hr2_eq]
      exact Real.rpow_pos_of_pos (by norm_num) _
    exact lt_min h1 h2

  have hr0_le_r2 : r0 ≤ r2 := by
    have h : r0 = min (Real.rpow K (-(1 / τ))) r2 := by rfl
    rw [h]
    exact min_le_right _ _

  have hr2_le_one : r2 ≤ 1 := by
    rw [hr2_eq]
    have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have h : (2 : ℝ) ^ (-(N : ℝ)) ≤ (2 : ℝ) ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using h

  -- Convert h_scale_r2 to use κ notation
  have h_scale_r2κ : Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r2 (-(ε_F - 8 * τ - 2 * κ)) >
      80000 * Real.rpow r2 (-κ) := by
    have hκ_eq : κ = 14 * τ / (1 - σ) := by rfl
    simpa [hκ_eq] using h_scale_r2

  -- Step 10: Propagate scale conditions from r2 to all r ≤ r0
  have h_scale_r0 : ∀ (r : ℝ), 0 < r → r ≤ r0 →
      (Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-(ε_F - 8 * τ - 2 * κ)) >
        80000 * Real.rpow r (-κ)) ∧
      (Real.rpow r τ ≤ 1 / 6) ∧
      (2 * r ≤ (Real.sqrt 3 / 2) * Real.rpow r κ) ∧
      (4 * r / (Real.rpow r κ / 4) ≤ 1) := by
    intro r hr hr_le
    have h_r_le_r2 : r ≤ r2 := le_trans hr_le hr0_le_r2
    have hr2_pos : 0 < r2 := by
      rw [hr2_eq]; exact Real.rpow_pos_of_pos (by norm_num) _
    set p : ℝ := ε_F - 8 * τ - 3 * κ with hp_def
    have hp_pos : 0 < p := by linarith [hεF_large3]
    -- Condition 1: scale inequality via ratio f(r) = 2^(-(2σ+ε_F)) * r^(-p)
    have h_rp_pos : 0 < Real.rpow r p := Real.rpow_pos_of_pos hr _
    have h_r2p_pos : 0 < Real.rpow r2 p := Real.rpow_pos_of_pos hr2_pos _
    have h_pos_pow_le : Real.rpow r p ≤ Real.rpow r2 p :=
      Real.rpow_le_rpow (by linarith) h_r_le_r2 (by linarith)
    have h_neg_pow_ge : Real.rpow r (-p) ≥ Real.rpow r2 (-p) := by
      have h1 : Real.rpow r (-p) = (Real.rpow r p)⁻¹ := Real.rpow_neg (by linarith) p
      have h2 : Real.rpow r2 (-p) = (Real.rpow r2 p)⁻¹ := Real.rpow_neg (by linarith) p
      rw [h1, h2]
      have h_goal : 1 / Real.rpow r2 p ≤ 1 / Real.rpow r p :=
        one_div_le_one_div_of_le h_rp_pos h_pos_pow_le
      simpa [one_div] using h_goal
    have h2pos : 0 ≤ Real.rpow 2 (-(2 * σ + ε_F)) := Real.rpow_nonneg (by norm_num) _
    have h_f_ge : Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-p) ≥
        Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r2 (-p) := by
      exact mul_le_mul_of_nonneg_left h_neg_pow_ge h2pos
    have h_exp_add : -(ε_F - 8 * τ - 3 * κ) + (-κ) = -(ε_F - 8 * τ - 2 * κ) := by ring
    have h9 : Real.rpow r2 (-(ε_F - 8 * τ - 2 * κ)) =
        Real.rpow r2 (-p) * Real.rpow r2 (-κ) := by
      have h_add : Real.rpow r2 (-p + (-κ)) = Real.rpow r2 (-p) * Real.rpow r2 (-κ) :=
        Real.rpow_add hr2_pos (-p) (-κ)
      have h_eq : -p + (-κ) = -(ε_F - 8 * τ - 2 * κ) := by
        simp only [hp_def] <;> ring
      rw [h_eq] at h_add
      exact h_add
    have h_r2_kappa_pos : 0 < Real.rpow r2 (-κ) := Real.rpow_pos_of_pos hr2_pos _
    have h_f2_gt : Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r2 (-p) > 80000 := by
      have h_subst : Real.rpow 2 (-(2 * σ + ε_F)) * (Real.rpow r2 (-p) * Real.rpow r2 (-κ)) >
          80000 * Real.rpow r2 (-κ) := by
        rw [←h9]
        exact h_scale_r2κ
      have h : (Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r2 (-p)) * Real.rpow r2 (-κ) >
          80000 * Real.rpow r2 (-κ) := by
        simpa [mul_assoc] using h_subst
      by_contra h_cont
      have h_le : (Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r2 (-p)) * Real.rpow r2 (-κ) ≤
          80000 * Real.rpow r2 (-κ) := by
        gcongr
        <;> linarith
      linarith
    have h_f_gt : Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-p) > 80000 :=
      lt_of_lt_of_le h_f2_gt h_f_ge
    have h12 : Real.rpow r (-(ε_F - 8 * τ - 2 * κ)) =
        Real.rpow r (-p) * Real.rpow r (-κ) := by
      have h_add : Real.rpow r (-p + (-κ)) = Real.rpow r (-p) * Real.rpow r (-κ) :=
        Real.rpow_add hr (-p) (-κ)
      have h_eq : -p + (-κ) = -(ε_F - 8 * τ - 2 * κ) := by
        simp only [hp_def] <;> ring
      rw [h_eq] at h_add
      exact h_add
    have h_r_kappa_pos : 0 < Real.rpow r (-κ) := Real.rpow_pos_of_pos hr _
    have h1 : Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-(ε_F - 8 * τ - 2 * κ)) >
          80000 * Real.rpow r (-κ) := by
      rw [h12]
      have h : (Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-p)) * Real.rpow r (-κ) >
          80000 * Real.rpow r (-κ) :=
        mul_lt_mul_of_pos_right h_f_gt h_r_kappa_pos
      simpa [mul_assoc] using h
    -- Condition 2: r^τ ≤ 1/6
    have h2 : Real.rpow r τ ≤ Real.rpow r2 τ := Real.rpow_le_rpow (by linarith) h_r_le_r2 (by linarith)
    have h2' : Real.rpow r τ ≤ 1 / 6 := le_trans h2 h_r2_tau_le
    -- Condition 3: 2r ≤ (√3/2) * r^κ
    have h3 : Real.rpow r (1 - κ) ≤ Real.rpow r2 (1 - κ) :=
      Real.rpow_le_rpow (by linarith) h_r_le_r2 (by linarith)
    have h3' : Real.rpow r (1 - κ) ≤ Real.sqrt 3 / 4 := le_trans h3 h_r2_1mkappa_le_sqrt34
    have h_rk_pos : 0 < Real.rpow r κ := Real.rpow_pos_of_pos hr _
    have h_div_eq : Real.rpow r (1 - κ) = r / Real.rpow r κ := by
      have h_sub : Real.rpow r (1 - κ) = Real.rpow r 1 / Real.rpow r κ :=
        Real.rpow_sub (by linarith) 1 κ
      have h_r1 : Real.rpow r 1 = r := Real.rpow_one r
      rw [h_sub, h_r1]
    have h3'' : 2 * r ≤ (Real.sqrt 3 / 2) * Real.rpow r κ := by
      have h_ineq : r / Real.rpow r κ ≤ Real.sqrt 3 / 4 := by
        rw [←h_div_eq]; exact h3'
      have h : 2 * r = 2 * Real.rpow r κ * (r / Real.rpow r κ) := by
        field_simp [h_rk_pos.ne'] <;> ring
      rw [h]
      have h2 : 2 * Real.rpow r κ * (r / Real.rpow r κ) ≤ 2 * Real.rpow r κ * (Real.sqrt 3 / 4) := by
        gcongr
      have h3 : 2 * Real.rpow r κ * (Real.sqrt 3 / 4) = (Real.sqrt 3 / 2) * Real.rpow r κ := by ring
      rw [h3] at h2
      exact h2
    -- Condition 4: 4r / (r^κ/4) ≤ 1
    have h4 : Real.rpow r (1 - κ) ≤ 1 / 16 := le_trans h3 h_r2_1mkappa_le_116
    have h4' : 4 * r / (Real.rpow r κ / 4) ≤ 1 := by
      have h_ineq2 : r / Real.rpow r κ ≤ 1 / 16 := by
        rw [←h_div_eq]; exact h4
      have h_eq2 : 4 * r / (Real.rpow r κ / 4) = 16 * (r / Real.rpow r κ) := by
        field_simp [h_rk_pos.ne'] <;> ring
      rw [h_eq2]
      have h : 16 * (r / Real.rpow r κ) ≤ 16 * (1 / 16 : ℝ) := by gcongr
      have h2 : 16 * (1 / 16 : ℝ) = 1 := by norm_num
      rw [h2] at h
      exact h
    exact ⟨h1, h2', h3'', h4'⟩

  -- hC_X_bound_r0 from r2 condition via monotonicity (negative exponent reverses)
  have hC_X_bound_r0 : C_X_const * (D_X : ℝ) ≤ Real.rpow (2 * r0) (-ε_F) := by
    have h1 : C_X_const * (D_X : ℝ) ≤ Real.rpow (2 * r2) (-ε_F) := h_C_X_D_X_r2.1
    have h3 : 0 < 2 * r0 := by positivity
    have h4 : 0 < 2 * r2 := by
      have h41 : 0 < r2 := by
        rw [hr2_eq]
        exact Real.rpow_pos_of_pos (by norm_num) _
      linarith
    have h5 : Real.rpow (2 * r0) ε_F ≤ Real.rpow (2 * r2) ε_F :=
      Real.rpow_le_rpow (by positivity) (by gcongr) (by linarith)
    have h6 : Real.rpow (2 * r2) (-ε_F) ≤ Real.rpow (2 * r0) (-ε_F) := by
      have h61 : Real.rpow (2 * r0) (-ε_F) = (Real.rpow (2 * r0) ε_F)⁻¹ :=
        Real.rpow_neg (by positivity) ε_F
      have h62 : Real.rpow (2 * r2) (-ε_F) = (Real.rpow (2 * r2) ε_F)⁻¹ :=
        Real.rpow_neg (by positivity) ε_F
      rw [h61, h62]
      have h_pos1 : 0 < Real.rpow (2 * r0) ε_F := Real.rpow_pos_of_pos (by positivity) _
      have h_pos2 : 0 < Real.rpow (2 * r2) ε_F := Real.rpow_pos_of_pos (by positivity) _
      have h_inv : (Real.rpow (2 * r2) ε_F)⁻¹ ≤ (Real.rpow (2 * r0) ε_F)⁻¹ := by
        gcongr
        <;> linarith
      exact h_inv
    exact le_trans h1 h6

  -- hδ_le_r0 from inner conclusion
  have hδ_le_r0 : 2 * r0 ≤ δ_star := by
    calc 2 * r0 ≤ 2 * r2 := by gcongr
         _ ≤ δ_star := h_2r2_le_delta

  -- hK'_r0_large and hK'_r0_lower from inner conclusion
  have hK'_r0_large : (2 : ℝ) ^ (σ + τ) < K' * r0 ^ (σ + τ) := by
    simpa [hr0_eq, hK'_def] using hK'_r0_large_r2
  have hK'_r0_lower : K' / (2 : ℝ) ^ (σ + τ) ≥ 2 * r0 ^ (2 * τ) := by
    simpa [hr0_eq, hK'_def] using hK'_r0_lower_r2

  -- Remaining conditions needing small-r lemmas
  rcases ConcentratedParam.concentrated_param_selection_bounded
      hσ_pos hσ_lt_one hτ (hτ_small_all σ hσ) rfl hC hK with
    ⟨r_conc, hr_conc_pos, h_conc_spec⟩

  have hτ_lt_εF : τ < ε_F := by
    have h : 8 * τ + 3 * κ < ε_F := hεF_large3
    have hκ_nonneg : 0 ≤ κ := by positivity
    linarith

  rcases C_X_bound_for_small_r τ ε_F C hτ hεF_pos hτ_lt_εF hC D_X hD_X_pos with
    ⟨r_ext, hr_ext_pos, h_ext_spec⟩

  -- Define C_B threshold and r_max
  let r_CB : ℝ := Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
      (-1 / (ε_F - κ - 5 * τ))
  let r_max : ℝ := min r_CB (min r_conc (min r_ext (Real.rpow K (-(1 / τ)) / 2)))
  have hr_CB_pos : 0 < r_CB := CBBound.cB_threshold_pos hK hσ_pos.le hεF_pos hεF_large3 hκ_pos hτ hD_T_pos
  have hr_max_pos : 0 < r_max := by
    have h1 : 0 < r_CB := hr_CB_pos
    have h2 : 0 < r_conc := hr_conc_pos
    have h3 : 0 < r_ext := hr_ext_pos
    have h4 : 0 < Real.rpow K (-(1 / τ)) / 2 := by
      have h5 : 0 < K := by linarith
      have h6 : 0 < Real.rpow K (-(1 / τ)) := Real.rpow_pos_of_pos h5 _
      positivity
    positivity
  have hr_max_le_r_CB : r_max ≤ r_CB := min_le_left _ _
  have hr_max_le_r_conc : r_max ≤ r_conc := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_max_le_r_ext : r_max ≤ r_ext := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_max_le_Kinv_half : r_max ≤ Real.rpow K (-(1 / τ)) / 2 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hr_max_lt_Kinv : r_max < Real.rpow K (-(1 / τ)) := by
    have h1 : r_max ≤ Real.rpow K (-(1 / τ)) / 2 := hr_max_le_Kinv_half
    have h2 : 0 < Real.rpow K (-(1 / τ)) := Real.rpow_pos_of_pos (by linarith) _
    linarith
  have hr_max_le_min : r_max ≤ min r_conc r_ext := by
    have h1 : r_max ≤ r_conc := hr_max_le_r_conc
    have h2 : r_max ≤ r_ext := hr_max_le_r_ext
    exact le_min h1 h2

  -- hB_large: r_max > 4 / K'^(1/(σ+τ))
  have hτ_le_tau_max_Q : τ ≤ τ_max_Q := by
    dsimp only [τ]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hτ2_Q : τ^2 ≤ 4000 / Q_min := by
    have h4 : τ ≤ Real.sqrt (4000 / Q_min) := hτ_le_tau_max_Q
    have h5 : 0 ≤ τ := by linarith
    have h6 : 0 ≤ 4000 / Q_min := by positivity
    have h7 : τ^2 ≤ (Real.sqrt (4000 / Q_min))^2 := by
      gcongr <;> linarith
    have h8 : (Real.sqrt (4000 / Q_min))^2 = 4000 / Q_min := Real.sq_sqrt h6
    rw [h8] at h7
    exact h7
  have hτ_lt_one : τ < 1 := by linarith [hτ_lt_01]
  rcases construct_Q_and_bounds Q_min τ M c C K hτ hτ_lt_one hM_gt400 hc hC hK hQ_min_pos hτ2_Q
    with ⟨Q, hQ_def, hQ_large, hQ_min_le, hK_le_Q, hC_le_Q⟩
  have hQ_huge : Q ≥ (2 : ℝ)^(ε_F + 2) := by
    have h1 : Q_min ≥ (2 : ℝ)^(ε_F + 2) := by
      dsimp only [Q_min]; exact le_max_left _ _
    exact h1.trans hQ_min_le
  have hDT_le_Q : (D_T : ℝ) ≤ Q := by
    have hDT_eq : (D_T : ℝ) = (D_T_const : ℝ) := by rfl
    have h2 : (D_T : ℝ) ≤ Q_min := by
      rw [hDT_eq]
      dsimp only [Q_min]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact h2.trans hQ_min_le
  have hDX_le_Q : (D_X : ℝ) ≤ Q := by
    have hDX_eq : (D_X : ℝ) = (D_X_const : ℝ) := by rfl
    have h2 : (D_X : ℝ) ≤ Q_min := by
      rw [hDX_eq]
      dsimp only [Q_min]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact h2.trans hQ_min_le
  have hτ_small : τ < 1 / 14 := by linarith [hτ_lt_01]
  have hστ_pos : 0 < σ + τ := by linarith [hσ_pos, hτ]
  have hστ_lt_two : σ + τ < 2 := by linarith [hσ_lt_one, hτ_lt_01]
  have hκ_nonneg : 0 ≤ κ := by positivity
  -- Equalities for r_max components
  have hr_conc_eq : r_conc = ConcentratedParam.concentrated_r_conc σ τ C K κ := h_conc_spec.1
  have hr_ext_eq : r_ext = c_x_r_ext τ ε_F C D_X := h_ext_spec.1
  have hr_CB_eq : r_CB = Real.rpow (Real.rpow (2 : ℝ) (-ε_F) /
      (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7)) (1 / (ε_F - κ - 5 * τ)) := by
    set A_CB : ℝ := 60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 with hA_CB_def
    set e_CB : ℝ := ε_F - κ - 5 * τ with he_CB_def
    have hA_CB_pos : 0 < A_CB := by positivity
    have h2neg_pos : 0 < Real.rpow (2 : ℝ) (-ε_F) := Real.rpow_pos_of_pos (by norm_num) _
    have hB_CB_pos : 0 < A_CB / Real.rpow (2 : ℝ) (-ε_F) := by positivity
    set B : ℝ := A_CB / Real.rpow (2 : ℝ) (-ε_F) with hB_def
    have hB_pos : 0 < B := hB_CB_pos
    have hBinv_pos : 0 < B⁻¹ := by positivity
    have h_inv : B⁻¹ = Real.rpow (2 : ℝ) (-ε_F) / A_CB := by
      rw [hB_def]
      field_simp [hA_CB_pos.ne', h2neg_pos.ne'] <;> ring
    have h_log1 : Real.log (Real.rpow B (-1 / e_CB)) = (-1 / e_CB) * Real.log B :=
      Real.log_rpow hB_pos (-1 / e_CB)
    have h_log2 : Real.log (Real.rpow (B⁻¹) (1 / e_CB)) = (1 / e_CB) * Real.log (B⁻¹) :=
      Real.log_rpow hBinv_pos (1 / e_CB)
    have h_log_inv : Real.log (B⁻¹) = -Real.log B := by rw [Real.log_inv]
    have h_eq : Real.log (Real.rpow B (-1 / e_CB)) = Real.log (Real.rpow (B⁻¹) (1 / e_CB)) := by
      rw [h_log1, h_log2, h_log_inv] <;> ring
    have h_pos1 : 0 < Real.rpow B (-1 / e_CB) := Real.rpow_pos_of_pos hB_pos _
    have h_pos2 : 0 < Real.rpow (B⁻¹) (1 / e_CB) := Real.rpow_pos_of_pos hBinv_pos _
    have h_main : Real.rpow B (-1 / e_CB) = Real.rpow (B⁻¹) (1 / e_CB) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos1) (Set.mem_Ioi.mpr h_pos2) h_eq
    have h_r_CB_eq : r_CB = Real.rpow B (-1 / e_CB) := by rfl
    rw [h_r_CB_eq, h_main, h_inv]
  have hr_max_eq : r_max = min r_CB (min r_conc (min r_ext (Real.rpow K (-(1 / τ)) / 2))) := by
    dsimp only [r_max]
    <;> rfl
  have hB_large : r_max > 4 / K'^(1 / (σ + τ)) :=
    prove_hB_large c Q M σ τ ε_F κ C K K' D_T D_X
      r_conc r_ext r_CB r_max
      hQ_large hM_gt400 hτ hτ_lt_one hτ_small hστ_pos hστ_lt_two
      hσ_pos hσ_lt_one (hτ_small_all σ hσ) hεF_large3 hκ_nonneg hκ_lt_one
      hC hK hK_le_Q hC_le_Q hD_T_pos hD_X_pos hDT_le_Q hDX_le_Q hQ_huge
      hK'_def hQ_def hr_conc_eq hr_ext_eq hr_CB_eq hr_max_eq

  -- Symmetric distance (doesn't depend on r0)
  have h_set_eq : {d : ℝ | ∃ x ∈ (ν₂ : Measure Point).support,
        ∃ y ∈ (ν₁ : Measure Point).support, dist x y = d} =
      {d : ℝ | ∃ x ∈ (ν₁ : Measure Point).support,
        ∃ y ∈ (ν₂ : Measure Point).support, dist x y = d} := by
    ext d
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, y, hy, h_eq⟩
      refine' ⟨y, hy, x, hx, _⟩
      rw [dist_comm] <;> exact h_eq
    · rintro ⟨y, hy, x, hx, h_eq⟩
      refine' ⟨x, hx, y, hy, _⟩
      rw [dist_comm] <;> exact h_eq
  have h_dist_symm : (1 : ℝ) / 2 ≤
      sInf {d : ℝ | ∃ x ∈ (ν₂ : Measure Point).support,
        ∃ y ∈ (ν₁ : Measure Point).support, dist x y = d} := by
    rw [h_set_eq] <;> exact h_dist

  by_cases h_case : r2 ≥ r_max
  · -- Case 1: r2 ≥ r_max, need to shrink r2
    have hr_max_le_r2 : r_max ≤ r2 := by linarith
    rcases refine_r2_smaller τ σ c K C M κ ε_F δ_star C_X_const (D_X : ℝ)
        hτ hτ_lt_01 hσ_pos hσ_lt_one hκ_pos hκ_lt_one hεF_pos hεF_large3
        hc hC hK (hM_gt2s σ hσ) hM_gt400
        r2 N hr2_eq h_geom_sum K' hK'_def
        r0 (by rfl) hK'_r0_large hK'_r0_lower
        h_r2_tau_le h_r2_kappa_le_half h_r2_1mkappa_le_sqrt34 h_r2_1mkappa_le_116
        h_2r2_le_delta h_scale_r2κ h_C_X_D_X_r2.1
        r_max hr_max_pos hr_max_le_r2 hB_large
      with ⟨r2', N', hr2_eq', h_geom_sum', hK'_large', hK'_lower',
        h_tau', h_kappa', h_sqrt34', h_116', h_delta', h_scale', h_CX', hr2'_lt_max⟩
    let r0' := r2'
    have hK_pos' : 0 < K := by linarith
    have hKinv_pos' : 0 < Real.rpow K (-(1 / τ)) :=
      Real.rpow_pos_of_pos hK_pos' (-(1 / τ))
    have hr2'_lt_Kinv : r2' < Real.rpow K (-(1 / τ)) := by
      calc r2' < r_max := hr2'_lt_max
           _ ≤ Real.rpow K (-(1 / τ)) / 2 := hr_max_le_Kinv_half
           _ < Real.rpow K (-(1 / τ)) := by
             have h : Real.rpow K (-(1 / τ)) / 2 < Real.rpow K (-(1 / τ)) := by
               linarith [hKinv_pos']
             exact h
    have hr0'_eq : r0' = chooseR0 K τ r2' hK hτ := by
      have h1 : chooseR0 K τ r2' hK hτ = min (Real.rpow K (-(1 / τ))) r2' := by
        rfl
      rw [h1]
      have h2 : min (Real.rpow K (-(1 / τ))) r2' = r2' := by
        apply min_eq_right
        exact hr2'_lt_Kinv.le
      rw [h2] <;> rfl
    have hr0'_le_r0 : r0' ≤ r0 := by
      have h1 : r0' ≤ r2 := by linarith [hr2'_lt_max, hr_max_le_r2]
      have h2 : r0' ≤ Real.rpow K (-(1 / τ)) := hr2'_lt_Kinv.le
      have h3 : r0 = min (Real.rpow K (-(1 / τ))) r2 := by
        simp [r0, chooseR0] <;> rfl
      rw [h3]
      exact le_min h2 h1
    have hr0'_small : r0' < min r_conc r_ext := by
      calc r0' = r2' := by rfl
           _ < r_max := hr2'_lt_max
           _ ≤ min r_conc r_ext := hr_max_le_min
    have hC_B_r0' : ∀ (r : ℝ), 0 < r → r ≤ r0' → r ≤ r_CB := by
      intro r _ hr_le
      have h1 : r ≤ r2' := by simpa using hr_le
      have h2 : r < r_max := lt_of_le_of_lt h1 hr2'_lt_max
      exact le_trans (le_of_lt h2) hr_max_le_r_CB
    have hC_B_r0'_full : ∀ (r : ℝ), 0 < r → r ≤ r0' →
        r ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
          (-1 / (ε_F - κ - 5 * τ)) := hC_B_r0'
    have h_scale_r0' : ∀ (r : ℝ), 0 < r → r ≤ r0' →
        (Real.rpow 2 (-(2 * σ + ε_F)) * Real.rpow r (-(ε_F - 8 * τ - 2 * κ)) >
          80000 * Real.rpow r (-κ)) ∧
        (Real.rpow r τ ≤ 1 / 6) ∧
        (2 * r ≤ (Real.sqrt 3 / 2) * Real.rpow r κ) ∧
        (4 * r / (Real.rpow r κ / 4) ≤ 1) := by
      intro r hr hr_le
      have h_r_le_r0 : r ≤ r0 := le_trans hr_le hr0'_le_r0
      exact h_scale_r0 r hr h_r_le_r0
    have hC_X_bound_r0' : C_X_const * (D_X : ℝ) ≤ Real.rpow (2 * r0') (-ε_F) := by
      have h_r0'_le_r0 : r0' ≤ r0 := hr0'_le_r0
      have hr2'_pos : 0 < r2' := by
        rw [hr2_eq']
        exact Real.rpow_pos_of_pos (by norm_num) _
      have h_r0'_pos : 0 < r0' := by
        have h : r0' = r2' := by rfl
        rw [h]; exact hr2'_pos
      have h_pos1 : 0 < 2 * r0' := by positivity
      have h_pos2 : 0 < 2 * r0 := by positivity
      have h_le : 2 * r0' ≤ 2 * r0 := by gcongr
      have h3 : (2 * r0')^ε_F ≤ (2 * r0)^ε_F := by gcongr <;> linarith
      have h4 : 0 < (2 * r0')^ε_F := by positivity
      have h5 : 1 / (2 * r0)^ε_F ≤ 1 / (2 * r0')^ε_F := one_div_le_one_div_of_le h4 h3
      have h6 : (2 * r0)^(-ε_F) = 1 / (2 * r0)^ε_F := by
        rw [Real.rpow_neg (by positivity)] <;> ring
      have h7 : (2 * r0')^(-ε_F) = 1 / (2 * r0')^ε_F := by
        rw [Real.rpow_neg (by positivity)] <;> ring
      have h_mon : (2 * r0)^(-ε_F) ≤ (2 * r0')^(-ε_F) := by
        rw [h6, h7]; exact h5
      exact le_trans hC_X_bound_r0 h_mon
    have hδ_le_r0' : 2 * r0' ≤ δ_star := by
      have h : 2 * r0' ≤ 2 * r0 := by gcongr
      exact le_trans h hδ_le_r0
    have h_conc_r0' : ∀ (r : ℝ), 0 < r → r ≤ r0' →
        r ≤ 1 / 8 ∧
        ∃ (N : ℕ), 0 < N ∧
          2 * (2 : ℝ) + r ≤ r * (2 : ℝ)^N ∧
          Real.rpow r (σ + 3 * τ) ≥ C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ) ∧
          Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 396 ∧
          Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 66 ∧
          (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
            (1 / 1584 : ℝ) * Real.rpow r (-τ) ∧
          Real.rpow r (-2 * τ) > (10^7 : ℝ) * K * C * Real.rpow ((2 + r) / 4) σ ∧
          Real.rpow r τ * Real.log (1 / r) ≤ (1 / 100 : ℝ) ∧
          20 * C * Real.rpow r τ < 1 ∧
          18 * C * r ≤ Real.rpow r (σ + 3 * τ) := by
      intro r hr hr_le
      have hlt : r < r_conc := by
        calc r ≤ r0' := hr_le
             _ < min r_conc r_ext := hr0'_small
             _ ≤ r_conc := min_le_left _ _
      exact h_conc_spec.2 r hr hlt
    have hC_X_extraction_bound' : ∀ (r : ℝ), 0 < r → r ≤ r0' →
        let m := Real.rpow r τ / 2
        let L := max 0 (Real.log (2000 * C / (m * r))) + 1
        let C_X := 100 * C * L / m
        C_X * (D_X : ℝ) ≤ Real.rpow (2 * r) (-ε_F) := by
      intro r hr hr_le
      have hlt : r < r_ext := by
        calc r ≤ r0' := hr_le
             _ < min r_conc r_ext := hr0'_small
             _ ≤ r_ext := min_le_right _ _
      exact h_ext_spec.2 r hr hlt
    have hK'_r0_large_choose : (2 : ℝ)^(σ + τ) < K' * (chooseR0 K τ r2' hK hτ)^(σ + τ) := by
      have h_min_eq : min (Real.rpow K (-(1 / τ))) r2' = r2' := by
        apply min_eq_right
        exact hr2'_lt_Kinv.le
      have h : (2 : ℝ)^(σ + τ) < K' * (min (Real.rpow K (-(1 / τ))) r2')^(σ + τ) := hK'_large'
      rw [h_min_eq] at h
      rw [←hr0'_eq]
      exact h
    have hK'_r0_lower_choose : K' / (2 : ℝ)^(σ + τ) ≥ 2 * (chooseR0 K τ r2' hK hτ)^(2 * τ) := by
      have h_min_eq : min (Real.rpow K (-(1 / τ))) r2' = r2' := by
        apply min_eq_right
        exact hr2'_lt_Kinv.le
      have h : K' / (2 : ℝ)^(σ + τ) ≥ 2 * (min (Real.rpow K (-(1 / τ))) r2')^(2 * τ) := hK'_lower'
      rw [h_min_eq] at h
      rw [←hr0'_eq]
      exact h
    have h_main12 : HasMeasureThinTubes (σ + τ) K' (3 * c) ν₁ ν₂ :=
      B1.bootstrapping_one_direction_G
        β ε σ c K C hβ hε hσ hc hK hC ν₁ ν₂ h_dist h_supp1 h_supp2
        hν₁_growth hν₂_growth h_thin12 h_thin21
        τ hτ (hτ_small_all σ hσ) hτ_small2
        M hM K' hK'_def
        r2' N' hr2_eq' h_geom_sum'
        hK'_r0_large_choose hK'_r0_lower_choose
        r0' hr0'_eq
        κ rfl hκ_lt_one
        ε_F δ_star hεF_pos hδ_star_pos hF_estimate
        hεF_large3 hC_B_r0'_full hδ_le_r0' h_scale_r0'
        C_X_const (by norm_num) hC_X_bound_r0'
        hC_X_extraction_bound' h_conc_r0'
    have h_main21 : HasMeasureThinTubes (σ + τ) K' (3 * c) ν₂ ν₁ :=
      B1.bootstrapping_one_direction_G
        β ε σ c K C hβ hε hσ hc hK hC ν₂ ν₁ h_dist_symm h_supp2 h_supp1
        hν₂_growth hν₁_growth h_thin21 h_thin12
        τ hτ (hτ_small_all σ hσ) hτ_small2
        M hM K' hK'_def
        r2' N' hr2_eq' h_geom_sum'
        hK'_r0_large_choose hK'_r0_lower_choose
        r0' hr0'_eq
        κ rfl hκ_lt_one
        ε_F δ_star hεF_pos hδ_star_pos hF_estimate
        hεF_large3 hC_B_r0'_full hδ_le_r0' h_scale_r0'
        C_X_const (by norm_num) hC_X_bound_r0'
        hC_X_extraction_bound' h_conc_r0'
    exact ⟨h_main12, h_main21⟩
  · -- Case 2: r2 < r_max, already small enough
    have h : r2 < r_max := by linarith
    have hK_pos : 0 < K := by linarith
    have hKinv_pos2 : 0 < Real.rpow K (-(1 / τ)) :=
      Real.rpow_pos_of_pos hK_pos (-(1 / τ))
    have hr2_lt_Kinv : r2 < Real.rpow K (-(1 / τ)) := by
      calc r2 < r_max := h
           _ ≤ Real.rpow K (-(1 / τ)) / 2 := hr_max_le_Kinv_half
           _ < Real.rpow K (-(1 / τ)) := by
             have h : Real.rpow K (-(1 / τ)) / 2 < Real.rpow K (-(1 / τ)) := by
               linarith [hKinv_pos2]
             exact h
    have hr0_eq2 : r0 = r2 := by
      have h1 : r0 = chooseR0 K τ r2 hK hτ := by rfl
      rw [h1]
      have h2 : chooseR0 K τ r2 hK hτ = min (Real.rpow K (-(1 / τ))) r2 := by rfl
      rw [h2]
      have h3 : min (Real.rpow K (-(1 / τ))) r2 = r2 := by
        apply min_eq_right
        exact hr2_lt_Kinv.le
      rw [h3] <;> rfl
    have hr0_small : r0 < min r_conc r_ext := by
      rw [hr0_eq2]
      calc r2 < r_max := h
           _ ≤ min r_conc r_ext := hr_max_le_min
    have hC_B_r0 : ∀ (r : ℝ), 0 < r → r ≤ r0 →
        r ≤ Real.rpow (60000 * K^2 * (34 : ℝ)^σ * (D_T : ℝ)^7 / Real.rpow (2 : ℝ) (-ε_F))
          (-1 / (ε_F - κ - 5 * τ)) := by
      intro r _ hr_le
      have h_r_le_r2 : r ≤ r2 := by
        rw [hr0_eq2] at hr_le; exact hr_le
      have h_r_lt_max : r < r_max := lt_of_le_of_lt h_r_le_r2 h
      exact le_trans (le_of_lt h_r_lt_max) hr_max_le_r_CB
    have h_conc_r0 : ∀ (r : ℝ), 0 < r → r ≤ r0 →
        r ≤ 1 / 8 ∧
        ∃ (N : ℕ), 0 < N ∧
          2 * (2 : ℝ) + r ≤ r * (2 : ℝ)^N ∧
          Real.rpow r (σ + 3 * τ) ≥ C * r + 792 * (N : ℝ) * Real.rpow r (σ + 4 * τ) ∧
          Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 396 ∧
          Real.rpow r τ * (((Nat.floor (16 * Real.pi * (2 : ℝ) / (1 / 2)) + 1 : ℕ) : ℝ)) * K * (2 : ℝ)^σ ≤ 66 ∧
          (Nat.ceil ((1 - κ) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) ≤
            (1 / 1584 : ℝ) * Real.rpow r (-τ) ∧
          Real.rpow r (-2 * τ) > (10^7 : ℝ) * K * C * Real.rpow ((2 + r) / 4) σ ∧
          Real.rpow r τ * Real.log (1 / r) ≤ (1 / 100 : ℝ) ∧
          20 * C * Real.rpow r τ < 1 ∧
          18 * C * r ≤ Real.rpow r (σ + 3 * τ) := by
      intro r hr hr_le
      have hlt : r < r_conc := by
        calc r ≤ r0 := hr_le
             _ < min r_conc r_ext := hr0_small
             _ ≤ r_conc := min_le_left _ _
      exact h_conc_spec.2 r hr hlt
    have hC_X_extraction_bound : ∀ (r : ℝ), 0 < r → r ≤ r0 →
        let m := Real.rpow r τ / 2
        let L := max 0 (Real.log (2000 * C / (m * r))) + 1
        let C_X := 100 * C * L / m
        C_X * (D_X : ℝ) ≤ Real.rpow (2 * r) (-ε_F) := by
      intro r hr hr_le
      have hlt : r < r_ext := by
        calc r ≤ r0 := hr_le
             _ < min r_conc r_ext := hr0_small
             _ ≤ r_ext := min_le_right _ _
      exact h_ext_spec.2 r hr hlt
    have h_main12 : HasMeasureThinTubes (σ + τ) K' (3 * c) ν₁ ν₂ :=
      B1.bootstrapping_one_direction_G
        β ε σ c K C hβ hε hσ hc hK hC ν₁ ν₂ h_dist h_supp1 h_supp2
        hν₁_growth hν₂_growth h_thin12 h_thin21
        τ hτ (hτ_small_all σ hσ) hτ_small2
        M hM K' hK'_def
        r2 N hr2_eq h_geom_sum
        hK'_r0_large hK'_r0_lower
        r0 hr0_eq
        κ rfl hκ_lt_one
        ε_F δ_star hεF_pos hδ_star_pos hF_estimate
        hεF_large3 hC_B_r0 hδ_le_r0 h_scale_r0
        C_X_const (by norm_num) hC_X_bound_r0
        hC_X_extraction_bound h_conc_r0
    have h_main21 : HasMeasureThinTubes (σ + τ) K' (3 * c) ν₂ ν₁ :=
      B1.bootstrapping_one_direction_G
        β ε σ c K C hβ hε hσ hc hK hC ν₂ ν₁ h_dist_symm h_supp2 h_supp1
        hν₂_growth hν₁_growth h_thin21 h_thin12
        τ hτ (hτ_small_all σ hσ) hτ_small2
        M hM K' hK'_def
        r2 N hr2_eq h_geom_sum
        hK'_r0_large hK'_r0_lower
        r0 hr0_eq
        κ rfl hκ_lt_one
        ε_F δ_star hεF_pos hδ_star_pos hF_estimate
        hεF_large3 hC_B_r0 hδ_le_r0 h_scale_r0
        C_X_const (by norm_num) hC_X_bound_r0
        hC_X_extraction_bound h_conc_r0
    exact ⟨h_main12, h_main21⟩

/-- Final theorem draft: radial bootstrapping for measure thin tubes.
  Uses radial_bootstrapping_main_case; boundary case reduces β to β/2. -/
theorem radial_bootstrapping_measure_thin_tubes_draft :
    ∀ β ε : ℝ, 0 < β → 0 < ε →
      ∃ τ : ℝ, 0 < τ ∧ ∃ M : ℝ, 1 ≤ M ∧ BootstrappingConclusion β ε τ M := by
  intro β ε hβ hε
  by_cases hβ_lt : β < 1 - ε
  · -- Main case: β < 1 - ε
    exact radial_bootstrapping_main_case β ε hβ hε hβ_lt
  · -- Boundary case: β ≥ 1 - ε
    by_cases hβ_gt : β > 1 - ε
    · -- β > 1 - ε: interval [β, 1-ε] is empty, vacuous
      refine' ⟨1 / 100, by norm_num, 1, by norm_num, _⟩
      intro σ c K C ν₁ ν₂ h_supp1 h_supp2 hσ hc hK hC h_dist hν₁_growth hν₂_growth h_thin12 h_thin21
      have h_cont : β ≤ 1 - ε := by linarith [hσ.1, hσ.2]
      linarith
    · -- β = 1 - ε: reduce to main case with β' = β / 2
      let β' := β / 2
      have hβ'_pos : 0 < β' := by positivity
      have hβ'_lt : β' < 1 - ε := by
        dsimp only [β']
        have h_eq : β = 1 - ε := by linarith
        rw [h_eq] <;> linarith
      rcases radial_bootstrapping_main_case β' ε hβ'_pos hε hβ'_lt with
        ⟨τ, hτ, M, hM, h_goal⟩
      refine' ⟨τ, hτ, M, hM, _⟩
      intro σ c K C ν₁ ν₂ h_supp1 h_supp2 hσ hc hK hC h_dist hν₁_growth hν₂_growth h_thin12 h_thin21
      have hσ' : σ ∈ Set.Icc β' (1 - ε) := by
        have h1 : β' ≤ β := by dsimp only [β']; linarith
        exact ⟨by linarith [h1, hσ.1], hσ.2⟩
      exact h_goal σ c K C ν₁ ν₂ h_supp1 h_supp2 hσ' hc hK hC h_dist hν₁_growth hν₂_growth h_thin12 h_thin21

end RadialBootstrapping
