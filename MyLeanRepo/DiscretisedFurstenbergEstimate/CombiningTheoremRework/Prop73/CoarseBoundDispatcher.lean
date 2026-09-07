module

/-
  Coarse bound for inductive step — case split on first scale class.

  Branches:
  - bad: trivial |TΔ| ≥ MΔ dominates, all polylog factors ≤ 1
  - normal: prop5 at t=s with polylog absorption (C_coarse ≥ K_p5)
  - good-small: improved incidence |TΔ| ≥ Δ^{-(2s+ε_imp)} dominates (abstract ε_imp)
  - good-large: prop5 at exponent u with extra (MΔ·Δ^s)^α factor

  Dispatcher takes universal K_p5 from uniform_prop5 as a common argument.
  Branch-specific data (S-set property, absorption inequality) is supplied
  by the caller via h_normal_data / h_good_data.

  Whiteprint node: combining_theorem_genuine / coarse_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseNormalBoundPolylog
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-! ========================================================================
    Bad branch
    ======================================================================== -/

lemma coarse_bound_bad
    {s ε_N : ℝ} {MΔ : ℕ} {K C_coarse C'_coarse : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hεN : 0 < ε_N)
    (hC_coarse_pos : 0 < C_coarse) (hC'_coarse_pos : 0 < C'_coarse)
    (hK_ge1 : 1 ≤ K)
    (δ Δ_coarse : ℝ) (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ_coarse)
    (hΔ_lt_one : Δ_coarse < 1)
    (hLΔ_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hδ_lt_one : δ < 1) (lam : ℝ) (hlam : 0 < lam)
    (TΔ_card : ℝ) (hTΔ_ge : TΔ_card ≥ (MΔ : ℝ))
    (PΔ : ℝ) (hPΔ_eq : PΔ = Δ_coarse) :
    TΔ_card ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
  let LΔ := Real.log (1 / Δ_coarse)
  have hLΔ_pos : 0 < LΔ := by positivity
  have h_exp_pos : 0 < -s + ε_N + 1 := by linarith
  have h6 : Real.rpow Δ_coarse (-s + ε_N) * PΔ = Real.rpow Δ_coarse (-s + ε_N + 1) := by
    rw [hPΔ_eq]
    have h_rpow1 : Real.rpow Δ_coarse 1 = Δ_coarse := by simp
    have h7 : Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse 1 =
        Real.rpow Δ_coarse ((-s + ε_N) + 1) := by
      have h_add : Real.rpow Δ_coarse ((-s + ε_N) + 1) =
          Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse 1 :=
        Real.rpow_add hΔ_pos (-s + ε_N) 1
      exact h_add.symm
    have h8 : (-s + ε_N) + 1 = -s + ε_N + 1 := by ring
    have h9 : Real.rpow Δ_coarse (-s + ε_N) * Δ_coarse = Real.rpow Δ_coarse (-s + ε_N + 1) := by
      have h10 : Real.rpow Δ_coarse (-s + ε_N) * Δ_coarse =
          Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse 1 := by rw [h_rpow1]
      rw [h10, h7, h8]
    exact h9
  have hLΔ_ge1' : 1 ≤ LΔ := hLΔ_ge1
  have h_le1 : Real.rpow LΔ (-C_coarse) ≤ 1 := by
    have h9 : -C_coarse ≤ 0 := by linarith
    have h10 : Real.rpow LΔ (-C_coarse) ≤ Real.rpow LΔ 0 :=
      Real.rpow_le_rpow_of_exponent_le hLΔ_ge1' h9
    simpa using h10
  have h_le2 : Real.rpow K (-C'_coarse) ≤ 1 := by
    have h9 : -C'_coarse ≤ 0 := by linarith
    have h10 : Real.rpow K (-C'_coarse) ≤ Real.rpow K 0 :=
      Real.rpow_le_rpow_of_exponent_le hK_ge1 h9
    simpa using h10
  have h_le3 : Real.rpow δ (C'_coarse * lam) ≤ 1 :=
    Real.rpow_le_one hδ_pos.le hδ_lt_one.le (by positivity)
  have h_le4 : Real.rpow Δ_coarse (-s + ε_N + 1) ≤ 1 :=
    Real.rpow_le_one hΔ_pos.le hΔ_lt_one.le (by linarith)
  have h2_nonneg : 0 ≤ Real.rpow K (-C'_coarse) := Real.rpow_nonneg (by linarith) _
  have h3_nonneg : 0 ≤ Real.rpow δ (C'_coarse * lam) := Real.rpow_nonneg hδ_pos.le _
  have h4_nonneg : 0 ≤ Real.rpow Δ_coarse (-s + ε_N + 1) := Real.rpow_nonneg hΔ_pos.le _
  have h_product_le_one : Real.rpow LΔ (-C_coarse) * Real.rpow K (-C'_coarse) *
      Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N + 1) ≤ 1 := by
    have h5 : Real.rpow LΔ (-C_coarse) * Real.rpow K (-C'_coarse) ≤ 1 := by
      calc _
        ≤ 1 * Real.rpow K (-C'_coarse) := by gcongr <;> exact h2_nonneg
        _ ≤ 1 * 1 := by gcongr <;> exact h2_nonneg
        _ = 1 := by norm_num
    have h6 : (Real.rpow LΔ (-C_coarse) * Real.rpow K (-C'_coarse)) *
        Real.rpow δ (C'_coarse * lam) ≤ 1 := by
      calc _
        ≤ 1 * Real.rpow δ (C'_coarse * lam) := by gcongr <;> exact h3_nonneg
        _ ≤ 1 * 1 := by gcongr <;> exact h3_nonneg
        _ = 1 := by norm_num
    calc _
      ≤ 1 * Real.rpow Δ_coarse (-s + ε_N + 1) := by gcongr <;> exact h4_nonneg
      _ ≤ 1 * 1 := by gcongr <;> exact h4_nonneg
      _ = 1 := by norm_num
  have h_goal : Real.rpow LΔ (-C_coarse) * (MΔ : ℝ) * Real.rpow K (-C'_coarse) *
      Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N) * PΔ ≤ (MΔ : ℝ) := by
    have h_assoc : Real.rpow LΔ (-C_coarse) * (MΔ : ℝ) * Real.rpow K (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N) * PΔ =
        (MΔ : ℝ) * (Real.rpow LΔ (-C_coarse) * Real.rpow K (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * (Real.rpow Δ_coarse (-s + ε_N) * PΔ)) := by ring
    rw [h_assoc, h6]
    have hM_nonneg : 0 ≤ (MΔ : ℝ) := by positivity
    have h : (MΔ : ℝ) * (Real.rpow LΔ (-C_coarse) * Real.rpow K (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N + 1)) ≤ (MΔ : ℝ) := by
      calc _
        ≤ (MΔ : ℝ) * 1 := mul_le_mul_of_nonneg_left h_product_le_one hM_nonneg
        _ = (MΔ : ℝ) := by ring
    exact h
  exact le_trans h_goal hTΔ_ge

/-! ========================================================================
    Normal branch — wrapper around bacon's CoarseNormalBoundPolylog

    Uses polylog absorption: C_coarse ≥ K_p5 absorbs C_P_coarse into log exponent.
    h_absorb: LΔ^(C_coarse - K_p5) ≥ K_p5 * C_P_coarse * 13 * 2^s * Δ^ε_N
    ======================================================================== -/

/-- Coarse bound for normal scale: wraps coarse_normal_bound_polylog.

    The caller must provide h_absorb (polylog absorption condition). -/
lemma coarse_bound_normal
    {m : ℕ} {s ε_N lam δ Δ_coarse : ℝ} {MΔ : ℕ}
    {CΔ C_P_coarse K_B1 K_p5 C_coarse C'_coarse : ℝ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    (hK_p5_pos : 0 < K_p5)
    (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (C_P C_T M : ℝ),
      0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
      ∀ (P : Finset (DSquare m)), P.Nonempty →
        IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_P P →
        (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : TubeFamily m),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
          (∀ p ∈ P, (M : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
            let T := P.biUnion fun p => Tp p
            (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
              (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((s - s) / (1 - s)))
    (hK_B1_ge1 : 1 ≤ K_B1)
    (hCΔ_pos : 0 < CΔ) (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K_B1 * Real.rpow δ (-lam))
    (hC_coarse_ge : C_coarse ≥ K_p5)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    (hΔ_coarse_pos : 0 < Δ_coarse)
    (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hlam : 0 < lam)
    (hs : 0 < s) (hεN : 0 < ε_N)
    (hCP_coarse_pos : 0 < C_P_coarse)
    (hCP_coarse_ge1 : 1 ≤ C_P_coarse)
    (hP_nonempty : coarseConfig.P₀.Nonempty)
    (hMΔ_pos : 0 < MΔ)
    (hP_set_coarse : IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse
      (finsetDyadicToDSquare coarseConfig.P₀))
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (h_diam_coarse : ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3)
    (h_unit_coarse : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1)
    (h_absorb : Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
       K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse ε_N) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) :=
  coarse_normal_bound_polylog
    hK_p5_pos hK_p5_ge1 hK_p5_spec
    hK_B1_ge1 hCΔ_pos hCΔ_ge1 hCΔ_le
    hC_coarse_ge hC'_coarse_ge1
    hm_ge2 hΔ_coarse_eq hΔ_coarse_pos hΔ_coarse_lt_one
    hδ_pos hδ_lt_one hlam hs hεN
    hCP_coarse_pos hCP_coarse_ge1 hP_nonempty hMΔ_pos
    hP_set_coarse h_slope_coarse h_diam_coarse h_unit_coarse
    h_absorb

/-! ========================================================================
    Good branch (work in progress)

    Follows BaseGood.lean pattern:
    - Large MΔ: prop5 at exponent u, extra factor (MΔ*Δ^s)^α
    - Small MΔ: improved incidence |TΔ| ≥ Δ^{-(2s+ε_G)} dominates

    Parameters:
    - u = min(t_j, 1), s < u ≤ 1
    - α = (u-s)/(1-s), γ = (η+2ε_G)(1-s)/(u-s), so γ*α = η+2ε_G
    - h_exp_condition: γ ≤ ε_G + lam + ε_N - η
    ======================================================================== -/

/-- Coarse bound for good scale — small MΔ case.

    When MΔ < Δ_coarse^{-s-γ}, improved incidence dominates.
    Target includes PΔ = Δ_coarse^{-η} for good scale:
      Lbar^{-C} · MΔ · K^{-C'} · δ^{C'λ} · Δ^{-s+ε_N-η}
    ≤ Δ^{-(2s+ε_G)}  (improved incidence)

    Key: δ^{C'λ} ≤ δ^λ ≤ Δ^{γ-ε_G-ε_N+η} for γ ≤ ε_G+λ+ε_N-η.
-/
lemma coarse_bound_good_small
    {m : ℕ} {s ε_imp η ε_N lam δ Δ_coarse : ℝ} {MΔ : ℕ}
    {K C_coarse C'_coarse γ : ℝ} {CΔ : ℝ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    (hs : 0 < s) (hε_imp : 0 < ε_imp) (hεN : 0 < ε_N) (hlam : 0 < lam)
    (hC_coarse_pos : 0 < C_coarse) (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hK_ge1 : 1 ≤ K) (hK_pos : 0 < K)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hγ_pos : 0 < γ)
    (h_budget : ε_N + ε_imp ≥ γ + η)
    (hM_small : (MΔ : ℝ) < Real.rpow Δ_coarse (-s - γ))
    (h_improved : (coarseConfig.T₀.card : ENNReal) ≥
      ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_imp)))) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N - η) := by
  let Lbar := Real.log (1 / Δ_coarse)
  have hLbar_pos : 0 < Lbar := by positivity
  have hLbar_ge1' : 1 ≤ Lbar := hLbar_ge1
  have hT_lower_real : (coarseConfig.T₀.card : ℝ) ≥ Real.rpow Δ_coarse (-(2 * s + ε_imp)) := by
    have h_nonneg : 0 ≤ Real.rpow Δ_coarse (-(2 * s + ε_imp)) := Real.rpow_nonneg hΔ_coarse_pos.le _
    exact ENNReal.ofReal_le_natCast.mp h_improved
  have hL_neg_C_le_one : Real.rpow Lbar (-C_coarse) ≤ 1 := by
    have h1 : -C_coarse ≤ 0 := by linarith
    have h2 : Real.rpow Lbar (-C_coarse) ≤ Real.rpow Lbar 0 :=
      Real.rpow_le_rpow_of_exponent_le hLbar_ge1' h1
    simpa using h2
  have hK_le_one : Real.rpow K (-C'_coarse) ≤ 1 := by
    have h6 : -C'_coarse ≤ -1 := by linarith
    have h7 : Real.rpow K (-C'_coarse) ≤ Real.rpow K (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hK_ge1 h6
    have h8 : Real.rpow K (-1 : ℝ) ≤ 1 := by
      have h9 : Real.rpow K (-1 : ℝ) = 1 / K := by
        have h10 : Real.rpow K (-1 : ℝ) = K⁻¹ := by simpa using Real.rpow_neg_one K
        rw [h10] <;> field_simp
      rw [h9]
      have h11 : 1 / K ≤ 1 := by
        have h12 : 1 ≤ K := hK_ge1
        have h13 : 0 < K := hK_pos
        exact (div_le_one h13).mpr h12
      exact h11
    exact le_trans h7 h8
  let a : ℝ := γ - ε_imp - ε_N + η
  have ha_nonpos : a ≤ 0 := by
    dsimp only [a]
    linarith [h_budget]
  have ha_le_lam : a ≤ lam := by
    linarith [hlam, ha_nonpos]
  have hδ_Δ_ineq : Real.rpow δ lam ≤ Real.rpow Δ_coarse a := by
    by_cases h : 0 ≤ a
    · -- a ≥ 0: Δ^a ≥ δ^a ≥ δ^λ
      have h1 : Real.rpow δ a ≥ Real.rpow δ lam :=
        Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le ha_le_lam
      have h2 : Real.rpow δ a ≤ Real.rpow Δ_coarse a :=
        Real.monotoneOn_rpow_Ici_of_exponent_nonneg h
          (Set.mem_Ici.mpr hδ_pos.le) (Set.mem_Ici.mpr hΔ_coarse_pos.le) hδ_le_delta
      linarith
    · -- a < 0: Δ^a > 1 > δ^λ
      have h3 : a < 0 := by linarith
      have h4 : Real.rpow Δ_coarse (0 : ℝ) < Real.rpow Δ_coarse a :=
        Real.rpow_lt_rpow_of_exponent_gt (hx0 := hΔ_coarse_pos) (hx1 := hΔ_coarse_lt_one) (hyz := h3)
      have h4' : (1 : ℝ) < Real.rpow Δ_coarse a := by simpa using h4
      have h5 : Real.rpow δ lam < 1 :=
        Real.rpow_lt_one hδ_pos.le hδ_lt_one hlam
      linarith
  have hδC_le : Real.rpow δ (C'_coarse * lam) ≤ Real.rpow δ lam := by
    have h7 : C'_coarse * lam ≥ lam := by nlinarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h7
  have h_combine1 : Real.rpow Δ_coarse (-s - γ) * Real.rpow Δ_coarse (-s + ε_N - η) =
      Real.rpow Δ_coarse ((-s - γ) + (-s + ε_N - η)) :=
    (Real.rpow_add hΔ_coarse_pos (-s - γ) (-s + ε_N - η)).symm
  have h_exp_sum : (-s - γ) + (-s + ε_N - η) = -2 * s - γ + ε_N - η := by ring
  have h_final_exp : a + ((-s - γ) + (-s + ε_N - η)) = -(2 * s + ε_imp) := by
    dsimp only [a] <;> ring
  have h_posL : 0 < Real.rpow Lbar (-C_coarse) := Real.rpow_pos_of_pos hLbar_pos _
  have h7 : Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) <
      Real.rpow Lbar (-C_coarse) * Real.rpow Δ_coarse (-s - γ) :=
    mul_lt_mul_of_pos_left hM_small h_posL
  have h_pos_rpow1 : 0 ≤ Real.rpow Δ_coarse (-s + ε_N - η) := Real.rpow_nonneg hΔ_coarse_pos.le _
  have h_pos_rpow2 : 0 ≤ Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := Real.rpow_nonneg hΔ_coarse_pos.le _
  have h_posδ : 0 ≤ Real.rpow δ lam := Real.rpow_nonneg hδ_pos.le _
  have h6 : Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * Real.rpow K (-C'_coarse) *
      Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N - η) <
      Real.rpow Δ_coarse (-(2 * s + ε_imp)) := by
    have h_step1 : Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * Real.rpow K (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N - η) ≤
        Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * Real.rpow δ lam *
        Real.rpow Δ_coarse (-s + ε_N - η) := by
      have hA : Real.rpow K (-C'_coarse) ≤ 1 := hK_le_one
      have hB : Real.rpow δ (C'_coarse * lam) ≤ Real.rpow δ lam := hδC_le
      have h_posC : 0 ≤ Real.rpow δ (C'_coarse * lam) := Real.rpow_nonneg hδ_pos.le _
      have h : Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * Real.rpow K (-C'_coarse) *
          Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N - η) ≤
          Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * 1 *
          Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N - η) := by
        gcongr <;> linarith
      have h2 : Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * 1 *
          Real.rpow δ (C'_coarse * lam) * Real.rpow Δ_coarse (-s + ε_N - η) ≤
          Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * 1 *
          Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η) := by
        gcongr <;> exact h_posC
      calc _ ≤ _ := h
           _ ≤ _ := h2
           _ = _ := by ring
    have h_step2 : Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * Real.rpow δ lam *
        Real.rpow Δ_coarse (-s + ε_N - η) <
        Real.rpow Lbar (-C_coarse) * Real.rpow Δ_coarse (-s - γ) * Real.rpow δ lam *
        Real.rpow Δ_coarse (-s + ε_N - η) := by
      have hD_pos : 0 < Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η) := by
        have hD1 : 0 < Real.rpow δ lam := Real.rpow_pos_of_pos hδ_pos lam
        have hD2 : 0 < Real.rpow Δ_coarse (-s + ε_N - η) := Real.rpow_pos_of_pos hΔ_coarse_pos _
        exact mul_pos hD1 hD2
      have h7' : (Real.rpow Lbar (-C_coarse) * (MΔ : ℝ)) * (Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η)) <
          (Real.rpow Lbar (-C_coarse) * Real.rpow Δ_coarse (-s - γ)) * (Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η)) :=
        mul_lt_mul_of_pos_right h7 hD_pos
      have h_eq1 : Real.rpow Lbar (-C_coarse) * (MΔ : ℝ) * Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η) =
          (Real.rpow Lbar (-C_coarse) * (MΔ : ℝ)) * (Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η)) := by ring
      have h_eq2 : Real.rpow Lbar (-C_coarse) * Real.rpow Δ_coarse (-s - γ) * Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η) =
          (Real.rpow Lbar (-C_coarse) * Real.rpow Δ_coarse (-s - γ)) * (Real.rpow δ lam * Real.rpow Δ_coarse (-s + ε_N - η)) := by ring
      rw [h_eq1, h_eq2]
      exact h7'
    have h_step3 : Real.rpow Lbar (-C_coarse) * Real.rpow Δ_coarse (-s - γ) * Real.rpow δ lam *
        Real.rpow Δ_coarse (-s + ε_N - η) ≤
        Real.rpow δ lam * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := by
      have hE : Real.rpow Lbar (-C_coarse) ≤ 1 := hL_neg_C_le_one
      have hF : Real.rpow Δ_coarse (-s - γ) * Real.rpow Δ_coarse (-s + ε_N - η) =
          Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := by
        rw [h_combine1, h_exp_sum]
      calc
        Real.rpow Lbar (-C_coarse) * Real.rpow Δ_coarse (-s - γ) * Real.rpow δ lam *
            Real.rpow Δ_coarse (-s + ε_N - η)
          = Real.rpow Lbar (-C_coarse) * Real.rpow δ lam *
              (Real.rpow Δ_coarse (-s - γ) * Real.rpow Δ_coarse (-s + ε_N - η)) := by ring
        _ = Real.rpow Lbar (-C_coarse) * Real.rpow δ lam *
              Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := by rw [hF]
        _ ≤ 1 * Real.rpow δ lam * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := by
            have hG : 0 ≤ Real.rpow δ lam * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := by
              exact mul_nonneg h_posδ h_pos_rpow2
            nlinarith
        _ = Real.rpow δ lam * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := by ring
    have h_step4 : Real.rpow δ lam * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) ≤
        Real.rpow Δ_coarse (-(2 * s + ε_imp)) := by
      have hH : Real.rpow δ lam ≤ Real.rpow Δ_coarse a := hδ_Δ_ineq
      have hI : Real.rpow Δ_coarse a * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) =
          Real.rpow Δ_coarse (a + (-2 * s - γ + ε_N - η)) :=
        (Real.rpow_add hΔ_coarse_pos a (-2 * s - γ + ε_N - η)).symm
      have hJ : a + (-2 * s - γ + ε_N - η) = -(2 * s + ε_imp) := by
        dsimp only [a] <;> ring
      calc
        Real.rpow δ lam * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η)
          ≤ Real.rpow Δ_coarse a * Real.rpow Δ_coarse (-2 * s - γ + ε_N - η) := by
            exact mul_le_mul_of_nonneg_right hH h_pos_rpow2
        _ = Real.rpow Δ_coarse (a + (-2 * s - γ + ε_N - η)) := hI
        _ = Real.rpow Δ_coarse (-(2 * s + ε_imp)) := by rw [hJ]
    exact lt_of_le_of_lt h_step1 (lt_of_lt_of_le h_step2 (le_trans h_step3 h_step4))
  exact le_trans (le_of_lt h6) hT_lower_real

/-! ========================================================================
    Good branch — large MΔ case

    Uses prop5 at exponent u with extra factor (MΔ·Δ^s)^α.
    For MΔ ≥ Δ^{-s-γ}: (MΔ·Δ^s)^α ≥ Δ^{-γα} = Δ^{-(η+2ε_G)}.
    Polylog absorption: L^(C_coarse-K_u) ≥ K_u·C_P·13·2^s·Δ^(2ε_G+ε_N).
    ======================================================================== -/

/-- Coarse bound for good scale — large MΔ case.

    When MΔ ≥ Δ_coarse^{-s-γ}, prop5 at exponent u gives enough extra incidence.
    γ·α = η+2ε_G where α = (u-s)/(1-s). -/
lemma coarse_bound_good_large
    {m : ℕ} {s ε_G η ε_N lam δ Δ_coarse : ℝ} {MΔ : ℕ}
    {CΔ C_P_coarse K_B1 K_u C_coarse C'_coarse u γ : ℝ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    -- prop5 at exponent u
    (hK_u_pos : 0 < K_u)
    (hK_u_ge1 : 1 ≤ K_u)
    (hK_u_spec : ∀ (C_P C_T M : ℝ),
      0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
      ∀ (P : Finset (DSquare m)), P.Nonempty →
        IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) u C_P P →
        (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : TubeFamily m),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
          (∀ p ∈ P, (M : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
            let T := P.biUnion fun p => Tp p
            (T.card : ℝ) ≥ (1 / K_u) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_u) *
              (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((u - s) / (1 - s)))
    -- B1 bridge constant
    (hK_B1_ge1 : 1 ≤ K_B1)
    (hCΔ_pos : 0 < CΔ) (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K_B1 * Real.rpow δ (-lam))
    -- Coarse exponents
    (hC_coarse_ge : C_coarse ≥ K_u)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    -- exponent parameters
    (hs : 0 < s) (hs1 : s < 1)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hus : s < u) (hu1 : u ≤ 1)
    (hγ_pos : 0 < γ)
    (hγα : γ * ((u - s) / (1 - s)) = η + 2 * ε_G)
    -- scale data
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    (hΔ_coarse_pos : 0 < Δ_coarse)
    (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hlam : 0 < lam)
    -- coarse S-set at u and geometric data
    (hCP_coarse_pos : 0 < C_P_coarse)
    (hCP_coarse_ge1 : 1 ≤ C_P_coarse)
    (hP_nonempty : coarseConfig.P₀.Nonempty)
    (hMΔ_pos : 0 < MΔ)
    (hP_set_u : IsFinsetDeltaSSet (dyadicDelta m) u C_P_coarse
      (finsetDyadicToDSquare coarseConfig.P₀))
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (h_diam_coarse : ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3)
    (h_unit_coarse : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1)
    -- large-M condition
    (hM_large : (MΔ : ℝ) ≥ Real.rpow Δ_coarse (-s - γ))
    -- polylog absorption
    (h_absorb : Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_u) ≥
       K_u * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N)) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N - η) := by
  classical
  set Lc : ℝ := Real.log (1 / Δ_coarse) with hLc_def
  set C_T : ℝ := 13 * CΔ * Real.rpow 2 s with hCT_def
  set α : ℝ := (u - s) / (1 - s) with hα_def
  have hδ_eq : dyadicDelta m = Δ_coarse := hΔ_coarse_eq.symm
  have hδEI_eq : DiscretisedFurstenbergEstimate.δ m = dyadicDelta m := by
    simp [DiscretisedFurstenbergEstimate.δ, dyadicDelta] <;> ring
  have hLc_pos : 0 < Lc := by
    rw [hLc_def]
    apply Real.log_pos
    apply one_lt_one_div hΔ_coarse_pos hΔ_coarse_lt_one
  have hK_B1_pos : 0 < K_B1 := by linarith
  have h2s_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have hCT_pos : 0 < C_T := by rw [hCT_def] <;> positivity
  have hCT_ge1 : 1 ≤ C_T := by
    rw [hCT_def]
    have h1 : 1 ≤ CΔ := hCΔ_ge1
    have h2 : 1 ≤ Real.rpow 2 s := by apply Real.one_le_rpow <;> norm_num <;> linarith
    nlinarith
  have hα_pos : 0 < α := by
    rw [hα_def]
    have h1 : 0 < u - s := by linarith
    have h2 : 0 < 1 - s := by linarith
    exact div_pos h1 h2
  -- Step 1: Apply uniform_prop5 at exponent u
  have h_main : (coarseConfig.T₀.card : ℝ) ≥
      (1 / K_u) * Real.rpow (Real.log (1 / dyadicDelta m)) (-K_u) *
        (1 / (C_P_coarse * C_T)) * (MΔ : ℝ) * (dyadicDelta m) ^ (-s) *
        (((MΔ : ℝ) * (dyadicDelta m) ^ s) ^ α) := by
    have h_wrapper := uniform_prop5_wrapper_with_K
      (t := u) (hK_pos := hK_u_pos) (hK_spec := hK_u_spec)
      (config := coarseConfig) (hn_ge_2 := hm_ge2) (hM_pos := hMΔ_pos)
      (hP_nonempty := hP_nonempty) (hCP := hCP_coarse_pos) (hCP_ge1 := hCP_coarse_ge1)
      (hC₁ := hCΔ_pos) (hC1_ge1 := hCΔ_ge1)
      (hs_nonneg := by linarith) (hP_set := hP_set_u)
      (h_slope := h_slope_coarse) (h_diam := h_diam_coarse) (h_unit := h_unit_coarse)
    convert h_wrapper using 1
    <;> simp [hCT_def, hδEI_eq, hα_def] <;> ring
  rw [hδ_eq] at h_main
  -- Step 2: 1/C_T ≥ δ^lam / (13 * K_B1 * 2^s)
  have h_bound_CT : C_T ≤ 13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s := by
    rw [hCT_def]
    have h2 : CΔ ≤ K_B1 * Real.rpow δ (-lam) := hCΔ_le
    nlinarith
  have h1_inv : (1 : ℝ) / C_T ≥ Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s) := by
    have h_pos2 : 0 < 13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s := by
      have h1 : 0 < K_B1 := hK_B1_pos
      have h2 : 0 < Real.rpow δ (-lam) := Real.rpow_pos_of_pos hδ_pos _
      positivity
    have h3 : 1 / C_T ≥ 1 / (13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s) :=
      one_div_le_one_div_of_le hCT_pos h_bound_CT
    have h4 : 1 / (13 * K_B1 * Real.rpow δ (-lam) * Real.rpow 2 s) =
        Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s) := by
      have h_rpow_neg : Real.rpow δ (-lam) = (Real.rpow δ lam)⁻¹ := by
        simpa [Real.rpow_neg hδ_pos.le] using rfl
      rw [h_rpow_neg] <;> field_simp [hK_B1_pos.ne', h2s_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3
  -- Step 3: Large-M gives (MΔ * Δ^s)^α ≥ Δ^{-γα} = Δ^{-(η+2ε_G)}
  have hMΔΔs : (MΔ : ℝ) * Real.rpow Δ_coarse s ≥ Real.rpow Δ_coarse (-γ) := by
    have h1 : (MΔ : ℝ) ≥ Real.rpow Δ_coarse (-s - γ) := hM_large
    have h2 : Real.rpow Δ_coarse (-s - γ) * Real.rpow Δ_coarse s = Real.rpow Δ_coarse (-γ) := by
      have h3 : Real.rpow Δ_coarse (-s - γ) * Real.rpow Δ_coarse s =
          Real.rpow Δ_coarse ((-s - γ) + s) := (Real.rpow_add hΔ_coarse_pos (-s - γ) s).symm
      rw [h3] <;> ring_nf
    have h4 : (MΔ : ℝ) * Real.rpow Δ_coarse s ≥
        Real.rpow Δ_coarse (-s - γ) * Real.rpow Δ_coarse s := by
      gcongr
      <;> exact Real.rpow_nonneg hΔ_coarse_pos.le _
    rw [h2] at h4
    exact h4
  have h_base_ge1 : 1 ≤ Real.rpow Δ_coarse (-γ) := by
    have h_neg : -γ < 0 := by linarith [hγ_pos]
    have h' : Real.rpow Δ_coarse 0 < Real.rpow Δ_coarse (-γ) :=
      Real.rpow_lt_rpow_of_exponent_gt hΔ_coarse_pos hΔ_coarse_lt_one h_neg
    have h0 : Real.rpow Δ_coarse 0 = 1 := by simp
    rw [h0] at h'
    exact h'.le
  have h_power_lower : ((MΔ : ℝ) * Real.rpow Δ_coarse s) ^ α ≥ Real.rpow Δ_coarse (-(η + 2 * ε_G)) := by
    have h5 : ((MΔ : ℝ) * Real.rpow Δ_coarse s) ^ α ≥ (Real.rpow Δ_coarse (-γ)) ^ α :=
      Real.rpow_le_rpow (by positivity) hMΔΔs (by linarith)
    have h6 : (Real.rpow Δ_coarse (-γ)) ^ α = Real.rpow Δ_coarse (-γ * α) := by
      exact (Real.rpow_mul hΔ_coarse_pos.le (-γ) α).symm
    rw [h6] at h5
    have h7 : -γ * α = -(η + 2 * ε_G) := by
      have h8 : γ * α = η + 2 * ε_G := by
        rw [hα_def] <;> exact hγα
      linarith
    rw [h7] at h5
    exact h5
  -- Step 4: Weaken K_B1 and δ factors
  have hK_weaken : Real.rpow K_B1 (-C'_coarse) ≤ (1 / K_B1 : ℝ) := by
    have h6 : -C'_coarse ≤ -1 := by linarith
    have h7 : Real.rpow K_B1 (-C'_coarse) ≤ Real.rpow K_B1 (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hK_B1_ge1 h6
    have h8 : Real.rpow K_B1 (-1 : ℝ) = 1 / K_B1 := by
      have h9 : Real.rpow K_B1 (-1 : ℝ) = (Real.rpow K_B1 (1 : ℝ))⁻¹ := by
        simpa [Real.rpow_neg hK_B1_pos.le] using rfl
      rw [h9] <;> simp <;> ring
    rw [h8] at h7
    exact h7
  have hδ_weaken : Real.rpow δ (C'_coarse * lam) ≤ Real.rpow δ lam := by
    have h7 : C'_coarse * lam ≥ lam := by nlinarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h7
  -- Step 5: Polylog absorption (same structure as normal branch)
  have h_posLcK : 0 < Real.rpow Lc (C_coarse - K_u) := Real.rpow_pos_of_pos hLc_pos _
  set A : ℝ := K_u * C_P_coarse * 13 * Real.rpow 2 s with hA_def
  have hA_pos : 0 < A := by positivity
  set Y : ℝ := Real.rpow Δ_coarse (2 * ε_G + ε_N) with hY_def
  have hY_pos : 0 < Y := Real.rpow_pos_of_pos hΔ_coarse_pos _
  have h_const_absorb : (1 : ℝ) / A ≥ Real.rpow Lc (K_u - C_coarse) * Y := by
    set X : ℝ := Real.rpow Lc (C_coarse - K_u) with hX_def
    have hX_pos : 0 < X := Real.rpow_pos_of_pos hLc_pos _
    have h_absorb' : X ≥ A * Y := by simpa [hA_def, hX_def, hY_def] using h_absorb
    have h_main_goal : 1 / A ≥ X⁻¹ * Y := by
      have h : X ≥ A * Y := h_absorb'
      have h2 : X⁻¹ ≤ (A * Y)⁻¹ := by gcongr
      have h3 : (A * Y)⁻¹ = A⁻¹ * Y⁻¹ := by field_simp [hA_pos.ne', hY_pos.ne'] <;> ring
      rw [h3] at h2
      have h4 : X⁻¹ * Y ≤ A⁻¹ := by
        calc X⁻¹ * Y ≤ (A⁻¹ * Y⁻¹) * Y := by gcongr
             _ = A⁻¹ := by field_simp [hY_pos.ne'] <;> ring
      simpa [hA_def] using h4
    have h6 : Real.rpow Lc (K_u - C_coarse) = X⁻¹ := by
      have h7 : K_u - C_coarse = -(C_coarse - K_u) := by ring
      rw [h7]
      exact Real.rpow_neg hLc_pos.le (C_coarse - K_u)
    rw [h6]
    exact h_main_goal
  -- Multiply absorption with K_B1 and δ weakenings
  have h_goal2 : (1 / A) * (1 / K_B1) * Real.rpow δ lam ≥
      Real.rpow Lc (K_u - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * Y := by
    set X1 := (1 / A) with hX1_def
    set Y1 := Real.rpow Lc (K_u - C_coarse) * Y with hY1_def
    set X2 := (1 / K_B1 : ℝ) with hX2_def
    set Y2 := Real.rpow K_B1 (-C'_coarse) with hY2_def
    set X3 := Real.rpow δ lam with hX3_def
    set Y3 := Real.rpow δ (C'_coarse * lam) with hY3_def
    have hY1_pos : 0 < Y1 := mul_pos (Real.rpow_pos_of_pos hLc_pos _) hY_pos
    have hY2_pos : 0 < Y2 := Real.rpow_pos_of_pos hK_B1_pos _
    have hY3_pos : 0 < Y3 := Real.rpow_pos_of_pos hδ_pos _
    have hX1_pos : 0 < X1 := by positivity
    have hX2_pos : 0 < X2 := by positivity
    have hX3_pos : 0 < X3 := Real.rpow_pos_of_pos hδ_pos _
    have h1 : X1 ≥ Y1 := h_const_absorb
    have h2 : X2 ≥ Y2 := hK_weaken
    have h3 : X3 ≥ Y3 := hδ_weaken
    have h4 : X1 * X2 ≥ Y1 * Y2 := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h5 : X1 * X2 * X3 ≥ Y1 * Y2 * Y3 := mul_le_mul h4 h3 (by positivity) (by positivity)
    have h6 : Y1 * Y2 * Y3 = Real.rpow Lc (K_u - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * Y := by
      simp only [hY1_def, hY2_def, hY3_def] <;> ring
    rw [h6] at h5
    exact h5
  have h_posLc_negK : 0 < Real.rpow Lc (-K_u) := Real.rpow_pos_of_pos hLc_pos _
  have h_product : Real.rpow Lc (-K_u) * Real.rpow Lc (K_u - C_coarse) = Real.rpow Lc (-C_coarse) := by
    have h_add : Real.rpow Lc (-K_u) * Real.rpow Lc (K_u - C_coarse) =
        Real.rpow Lc ((-K_u) + (K_u - C_coarse)) :=
      (Real.rpow_add hLc_pos (-K_u) (K_u - C_coarse)).symm
    rw [h_add]
    have h_sum : (-K_u) + (K_u - C_coarse) = -C_coarse := by ring
    rw [h_sum]
  have h_absorb_main : (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) ≥
      Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
        Real.rpow δ (C'_coarse * lam) * Y := by
    have h_pos1 : 0 < (1 / K_u) * Real.rpow Lc (-K_u) * (1 / C_P_coarse) := by positivity
    have h_split2 : (1 / (C_P_coarse * C_T)) = (1 / C_P_coarse) * (1 / C_T) := by
      field_simp [hCP_coarse_pos.ne', hCT_pos.ne'] <;> ring
    have h_step1 : (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) ≥
        (1 / A) * Real.rpow Lc (-K_u) * (1 / K_B1) * Real.rpow δ lam := by
      have h9 : (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) =
          (1 / K_u) * Real.rpow Lc (-K_u) * ((1 / C_P_coarse) * (1 / C_T)) := by
        rw [h_split2] <;> ring
      rw [h9]
      have h_goal : (1 / K_u) * Real.rpow Lc (-K_u) * ((1 / C_P_coarse) * (1 / C_T)) ≥
          (1 / K_u) * Real.rpow Lc (-K_u) * ((1 / C_P_coarse) *
            (Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s))) := by
        gcongr
        <;> exact h1_inv
      have h_eq : (1 / K_u) * Real.rpow Lc (-K_u) * ((1 / C_P_coarse) *
            (Real.rpow δ lam / (13 * K_B1 * Real.rpow 2 s))) =
          (1 / A) * Real.rpow Lc (-K_u) * (1 / K_B1) * Real.rpow δ lam := by
        simp only [hA_def] <;> ring
      rw [h_eq] at h_goal
      exact h_goal
    have h_final_absorb : (1 / A) * Real.rpow Lc (-K_u) * (1 / K_B1) * Real.rpow δ lam ≥
        Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
          Real.rpow δ (C'_coarse * lam) * Y := by
      have h5 : Real.rpow Lc (-K_u) * ((1 / A) * (1 / K_B1) * Real.rpow δ lam) ≥
          Real.rpow Lc (-K_u) * (Real.rpow Lc (K_u - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
            Real.rpow δ (C'_coarse * lam) * Y) :=
        mul_le_mul_of_nonneg_left h_goal2 h_posLc_negK.le
      have h6 : Real.rpow Lc (-K_u) * (Real.rpow Lc (K_u - C_coarse) * Real.rpow K_B1 (-C'_coarse) *
            Real.rpow δ (C'_coarse * lam) * Y) =
          (Real.rpow Lc (-K_u) * Real.rpow Lc (K_u - C_coarse)) *
            (Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) * Y) := by ring
      have h7 : (Real.rpow Lc (-K_u) * Real.rpow Lc (K_u - C_coarse)) *
            (Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) * Y) =
          Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
            Real.rpow δ (C'_coarse * lam) * Y := by
        rw [h_product] <;> ring
      have h8 : (1 / A) * Real.rpow Lc (-K_u) * (1 / K_B1) * Real.rpow δ lam =
          Real.rpow Lc (-K_u) * ((1 / A) * (1 / K_B1) * Real.rpow δ lam) := by ring
      rw [h8]
      rw [h6, h7] at h5
      exact h5
    exact ge_trans h_step1 h_final_absorb
  -- Step 6: Final combine
  have h_pos_prod : 0 < (MΔ : ℝ) * Real.rpow Δ_coarse (-s) := by
    have h1 : 0 < (MΔ : ℝ) := by exact_mod_cast hMΔ_pos
    have h2 : 0 < Real.rpow Δ_coarse (-s) := Real.rpow_pos_of_pos hΔ_coarse_pos _
    exact mul_pos h1 h2
  have h_pos_eta : 0 < Real.rpow Δ_coarse (-(η + 2 * ε_G)) :=
    Real.rpow_pos_of_pos hΔ_coarse_pos _
  have h_pos_full : 0 < (MΔ : ℝ) * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G)) :=
    mul_pos h_pos_prod h_pos_eta
  have h_prefix_pos : 0 ≤ (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) *
      (MΔ : ℝ) * Real.rpow Δ_coarse (-s) := by
    have h1 : 0 < (1 / K_u) := by positivity
    have h2 : 0 < Real.rpow Lc (-K_u) := Real.rpow_pos_of_pos hLc_pos _
    have h3 : 0 < (1 / (C_P_coarse * C_T)) := by positivity
    have h4 : 0 < (MΔ : ℝ) := by exact_mod_cast hMΔ_pos
    have h5 : 0 < Real.rpow Δ_coarse (-s) := Real.rpow_pos_of_pos hΔ_coarse_pos _
    positivity
  have h_main2 : (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) *
      (MΔ : ℝ) * Real.rpow Δ_coarse (-s) *
      (((MΔ : ℝ) * Real.rpow Δ_coarse s) ^ α) ≥
    (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) *
      (MΔ : ℝ) * Real.rpow Δ_coarse (-s) *
      Real.rpow Δ_coarse (-(η + 2 * ε_G)) :=
    mul_le_mul_of_nonneg_left h_power_lower h_prefix_pos
  have h_add1 : Real.rpow Δ_coarse (2 * ε_G + ε_N) * Real.rpow Δ_coarse (-(η + 2 * ε_G)) *
      Real.rpow Δ_coarse (-s) = Real.rpow Δ_coarse (-s + ε_N - η) := by
    have h9 : Real.rpow Δ_coarse (2 * ε_G + ε_N) * Real.rpow Δ_coarse (-(η + 2 * ε_G)) =
        Real.rpow Δ_coarse (ε_N - η) := by
      have h10 : Real.rpow Δ_coarse (2 * ε_G + ε_N) * Real.rpow Δ_coarse (-(η + 2 * ε_G)) =
          Real.rpow Δ_coarse ((2 * ε_G + ε_N) + (-(η + 2 * ε_G))) :=
        (Real.rpow_add hΔ_coarse_pos (2 * ε_G + ε_N) (-(η + 2 * ε_G))).symm
      rw [h10]
      have h11 : (2 * ε_G + ε_N) + (-(η + 2 * ε_G)) = ε_N - η := by ring
      rw [h11]
    rw [h9]
    have h12 : Real.rpow Δ_coarse (ε_N - η) * Real.rpow Δ_coarse (-s) =
        Real.rpow Δ_coarse ((ε_N - η) + (-s)) :=
      (Real.rpow_add hΔ_coarse_pos (ε_N - η) (-s)).symm
    rw [h12] <;> ring_nf
  have h_final : (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow Lc (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N - η) := by
    calc
      (coarseConfig.T₀.card : ℝ)
        ≥ (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) *
            (MΔ : ℝ) * Real.rpow Δ_coarse (-s) *
            (((MΔ : ℝ) * Real.rpow Δ_coarse s) ^ α) := h_main
      _ ≥ (1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T)) *
            (MΔ : ℝ) * Real.rpow Δ_coarse (-s) *
            Real.rpow Δ_coarse (-(η + 2 * ε_G)) := h_main2
      _ = ((1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T))) *
            ((MΔ : ℝ) * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G))) := by ring
      _ ≥ (Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
               Real.rpow δ (C'_coarse * lam) * Y) *
            ((MΔ : ℝ) * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G))) := by
          have h : (Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
                     Real.rpow δ (C'_coarse * lam) * Y) *
                   ((MΔ : ℝ) * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G))) ≤
              ((1 / K_u) * Real.rpow Lc (-K_u) * (1 / (C_P_coarse * C_T))) *
                   ((MΔ : ℝ) * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G))) :=
            mul_le_mul_of_nonneg_right h_absorb_main h_pos_full.le
          exact h
      _ = Real.rpow Lc (-C_coarse) * (MΔ : ℝ) *
            Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
            Real.rpow Δ_coarse (-s + ε_N - η) := by
          have h13 : (Real.rpow Lc (-C_coarse) * Real.rpow K_B1 (-C'_coarse) *
                   Real.rpow δ (C'_coarse * lam) * Y) *
                 ((MΔ : ℝ) * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G))) =
              Real.rpow Lc (-C_coarse) * (MΔ : ℝ) *
                Real.rpow K_B1 (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
                (Y * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G))) := by ring
          rw [h13]
          have h14 : Y * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G)) =
              Real.rpow Δ_coarse (-s + ε_N - η) := by
            simp only [hY_def]
            have h15 : Y * Real.rpow Δ_coarse (-s) * Real.rpow Δ_coarse (-(η + 2 * ε_G)) =
                Real.rpow Δ_coarse (2 * ε_G + ε_N) * Real.rpow Δ_coarse (-(η + 2 * ε_G)) * Real.rpow Δ_coarse (-s) := by ring
            rw [h15]
            exact h_add1
          rw [h14] <;> ring
  exact h_final

/-! ========================================================================
    Case split dispatcher

    Consumes scaleClass0 and branch-specific data, dispatches to:
    - bad: coarse_bound_bad (PΔ = Δ_coarse)
    - normal: coarse_bound_normal (PΔ = 1)
    - good: split on MΔ ≥ Δ^{-s-γ}, then coarse_bound_good_large or _small (PΔ = Δ^{-η})
    ======================================================================== -/

/-- Dispatcher for the coarse first-scale bound.

    Cases on scaleClass0 and applies the appropriate branch lemma.
    For good scales, splits on MΔ ≥ Δ_coarse^{-s-γ}. -/
lemma coarse_bound_dispatcher
    {m : ℕ} {s ε_G η ε_N lam δ Δ_coarse : ℝ} {MΔ : ℕ}
    {K CΔ C_coarse C'_coarse : ℝ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    (scaleClass0 : ScaleClass)
    (PΔ : ℝ)
    -- common hypotheses
    (hs : 0 < s) (hs1 : s < 1) (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hlam : 0 < lam) (hK_ge1 : 1 ≤ K) (hK_pos : 0 < K)
    (hCΔ_pos : 0 < CΔ) (hCΔ_ge1 : 1 ≤ CΔ)
    (hCΔ_le : CΔ ≤ K * Real.rpow δ (-lam))
    (hC_coarse_pos : 0 < C_coarse) (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hm_ge2 : 2 ≤ m)
    (hΔ_coarse_eq : Δ_coarse = dyadicDelta m)
    (hΔ_coarse_pos : 0 < Δ_coarse) (hΔ_coarse_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hδ_le_delta : δ ≤ Δ_coarse)
    (hLbar_ge1 : 1 ≤ Real.log (1 / Δ_coarse))
    (hP_nonempty : coarseConfig.P₀.Nonempty)
    (hMΔ_pos : 0 < MΔ)
    (h_slope : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    (h_diam : ∀ (p q : DSquare m),
      p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      q ∈ finsetDyadicToDSquare coarseConfig.P₀ → dist p q ≤ 3)
    (h_unit : ∀ (p : DSquare m), p ∈ finsetDyadicToDSquare coarseConfig.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1)
    -- PΔ equalities based on scale class
    (hPΔ_bad : scaleClass0 = ScaleClass.bad → PΔ = Δ_coarse)
    (hPΔ_normal : scaleClass0 = ScaleClass.normal → PΔ = 1)
    (hPΔ_good : ∀ (t_j : ℝ), scaleClass0 = ScaleClass.good t_j → PΔ = Real.rpow Δ_coarse (-η))
    -- universal prop5 constant (from uniform_prop5, works for all t ∈ [s,1])
    (K_p5 : ℝ) (hK_p5_pos : 0 < K_p5) (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ m →
        ∀ (P : Finset (DSquare m)), P.Nonempty →
          IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t C_P P →
          (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
          (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
          ∀ (Tp : TubeFamily m),
            (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
            (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
            (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
            (∀ p ∈ P, (M : ℝ) / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
              let T := P.biUnion fun p => Tp p
              (T.card : ℝ) ≥ (1 / K_p5) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K_p5) *
                (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                  (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t - s) / (1 - s)))
    -- branch-specific data
    (h_normal_data : scaleClass0 = ScaleClass.normal →
      ∃ (C_P_coarse : ℝ), 1 ≤ C_P_coarse ∧ 0 < C_P_coarse ∧
        IsFinsetDeltaSSet (dyadicDelta m) s C_P_coarse (finsetDyadicToDSquare coarseConfig.P₀) ∧
        C_coarse ≥ K_p5 ∧
        Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
          K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse ε_N)
    (h_good_data : ∀ (t_j : ℝ), scaleClass0 = ScaleClass.good t_j →
      ∃ (u C_P_coarse γ ε_imp : ℝ), u = min t_j 1 ∧ s < u ∧ u ≤ 1 ∧
        1 ≤ C_P_coarse ∧ 0 < C_P_coarse ∧
        IsFinsetDeltaSSet (dyadicDelta m) u C_P_coarse (finsetDyadicToDSquare coarseConfig.P₀) ∧
        0 < γ ∧ γ * ((u - s) / (1 - s)) = η + 2 * ε_G ∧
        0 < ε_imp ∧ ε_N + ε_imp ≥ γ + η ∧
        C_coarse ≥ K_p5 ∧
        Real.rpow (Real.log (1 / Δ_coarse)) (C_coarse - K_p5) ≥
          K_p5 * C_P_coarse * 13 * Real.rpow 2 s * Real.rpow Δ_coarse (2 * ε_G + ε_N) ∧
        (coarseConfig.T₀.card : ENNReal) ≥
          ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_imp)))) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
  have hTΔ_ge : (coarseConfig.T₀.card : ℝ) ≥ (MΔ : ℝ) := by
    rcases hP_nonempty with ⟨p, hp⟩
    have h1 : coarseConfig.tubeFamily p hp ⊆ coarseConfig.T₀ := coarseConfig.h_subset p hp
    have h2 : (coarseConfig.tubeFamily p hp).card = MΔ := coarseConfig.h_size p hp
    have h3 : (coarseConfig.tubeFamily p hp).card ≤ coarseConfig.T₀.card := Finset.card_le_card h1
    rw [h2] at h3
    exact_mod_cast h3
  have h_rpow_combine : Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse (-η) =
      Real.rpow Δ_coarse (-s + ε_N - η) := by
    have h : Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse (-η) =
        Real.rpow Δ_coarse ((-s + ε_N) + (-η)) :=
      (Real.rpow_add hΔ_coarse_pos (-s + ε_N) (-η)).symm
    rw [h] <;> ring_nf
  cases scaleClass0 with
  | bad =>
    have hPΔ : PΔ = Δ_coarse := hPΔ_bad rfl
    exact coarse_bound_bad hs hs1 hεN hC_coarse_pos (by linarith) hK_ge1
      δ Δ_coarse hδ_pos hΔ_coarse_pos hΔ_coarse_lt_one hLbar_ge1 hδ_lt_one lam hlam
      (coarseConfig.T₀.card : ℝ) hTΔ_ge PΔ hPΔ
  | normal =>
    rcases h_normal_data rfl with ⟨C_P_coarse, hCP_ge1, hCP_pos, hP_set, hC_coarse_ge, h_absorb⟩
    have hK_p5_spec_s := hK_p5_spec s (by linarith) (by linarith)
    have hPΔ : PΔ = 1 := hPΔ_normal rfl
    rw [hPΔ]
    have h_main := coarse_bound_normal
      hK_p5_pos hK_p5_ge1 hK_p5_spec_s
      hK_ge1 hCΔ_pos hCΔ_ge1 hCΔ_le
      hC_coarse_ge hC'_coarse_ge1
      hm_ge2 hΔ_coarse_eq hΔ_coarse_pos hΔ_coarse_lt_one
      hδ_pos hδ_lt_one hlam hs hεN
      hCP_pos hCP_ge1 hP_nonempty hMΔ_pos
      hP_set h_slope h_diam h_unit h_absorb
    simpa using h_main
  | good t_j =>
    rcases h_good_data t_j rfl with ⟨u, C_P_coarse, γ, ε_imp, hu_eq, hus, hu1,
      hCP_ge1, hCP_pos, hP_set_u,
      hγ_pos, hγα, hε_imp_pos, h_budget, hC_coarse_ge, h_absorb, h_improved⟩
    have hK_p5_spec_u := hK_p5_spec u (le_of_lt hus) hu1
    have hPΔ : PΔ = Real.rpow Δ_coarse (-η) := hPΔ_good t_j rfl
    have h_goal : (coarseConfig.T₀.card : ℝ) ≥
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N - η) := by
      by_cases hM_large : (MΔ : ℝ) ≥ Real.rpow Δ_coarse (-s - γ)
      · exact coarse_bound_good_large
          hK_p5_pos hK_p5_ge1 hK_p5_spec_u
          hK_ge1 hCΔ_pos hCΔ_ge1 hCΔ_le
          hC_coarse_ge hC'_coarse_ge1
          hs hs1 hεG hη hεN hus hu1 hγ_pos hγα
          hm_ge2 hΔ_coarse_eq hΔ_coarse_pos hΔ_coarse_lt_one
          hδ_pos hδ_lt_one hlam
          hCP_pos hCP_ge1 hP_nonempty hMΔ_pos
          hP_set_u h_slope h_diam h_unit
          hM_large h_absorb
      · have hM_small : (MΔ : ℝ) < Real.rpow Δ_coarse (-s - γ) := lt_of_not_ge hM_large
        exact coarse_bound_good_small
          hs hε_imp_pos hεN hlam hC_coarse_pos hC'_coarse_ge1 hK_ge1 hK_pos
          hΔ_coarse_pos hΔ_coarse_lt_one hδ_pos hδ_lt_one hδ_le_delta hLbar_ge1
          hγ_pos h_budget hM_small h_improved
    have h_final_goal : (coarseConfig.T₀.card : ℝ) ≥
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
      have h11 : Real.rpow Δ_coarse (-s + ε_N) * PΔ = Real.rpow Δ_coarse (-s + ε_N - η) := by
        calc
          Real.rpow Δ_coarse (-s + ε_N) * PΔ
            = Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse (-η) := by rw [hPΔ]
          _ = Real.rpow Δ_coarse (-s + ε_N - η) := h_rpow_combine
      let A := Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
          Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)
      have h12 : A * Real.rpow Δ_coarse (-s + ε_N) * PΔ = A * Real.rpow Δ_coarse (-s + ε_N - η) := by
        have h13 : A * Real.rpow Δ_coarse (-s + ε_N) * PΔ = A * (Real.rpow Δ_coarse (-s + ε_N) * PΔ) := by ring
        rw [h13, h11] <;> ring
      rwa [h12]
    exact h_final_goal

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
