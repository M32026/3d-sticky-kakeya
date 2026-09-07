module

/-
  GoodImprovedIncidenceWrapper.lean

  Standalone wrapper for the good-case improved incidence lambda.
  Extracting from CIBW avoids whnf timeouts in the large theorem context.

  Whiteprint node: prop73 / good_improved_incidence_wrapper
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseAbsorptionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCaseImprovedIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformIncidenceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DirecretisedFurstenbergEstimate.RegularIncidence
open DiscretisedFurstenbergEstimate.BasicUniformization

/-- Derive `m ≥ τ*k` from `dyadicDelta m ≤ (dyadicDelta k)^τ`. -/
lemma scale_ratio_to_ge {k m : ℕ} {τ : ℝ} (hτ_pos : 0 < τ)
    (h : dyadicDelta m ≤ Real.rpow (dyadicDelta k) τ) :
    (m : ℝ) ≥ τ * (k : ℝ) := by
  have h9 : dyadicDelta m = Real.rpow 2 (-(m : ℝ)) := by
    simp [dyadicDelta] <;> norm_cast
  have h10 : Real.rpow (dyadicDelta k) τ = Real.rpow 2 (-(τ * (k : ℝ))) := by
    have h11 : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by simp [dyadicDelta] <;> norm_cast
    rw [h11]
    have h12 : Real.rpow (Real.rpow 2 (-(k : ℝ))) τ = Real.rpow 2 ((-(k : ℝ)) * τ) :=
      (Real.rpow_mul (by norm_num) (-(k : ℝ)) τ).symm
    rw [h12] <;> ring_nf
  rw [h9, h10] at h
  have h_pos1 : 0 < Real.rpow 2 (-(m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h_log : Real.log (Real.rpow 2 (-(m : ℝ))) ≤ Real.log (Real.rpow 2 (-(τ * (k : ℝ)))) :=
    Real.log_le_log h_pos1 h
  have h_log_m : Real.log (Real.rpow 2 (-(m : ℝ))) = -(m : ℝ) * Real.log 2 := by
    exact Real.log_rpow (by norm_num) (-(m : ℝ))
  have h_log_t : Real.log (Real.rpow 2 (-(τ * (k : ℝ)))) = -(τ * (k : ℝ)) * Real.log 2 := by
    exact Real.log_rpow (by norm_num) (-(τ * (k : ℝ)))
  rw [h_log_m, h_log_t] at h_log
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Algebra helper: `τε/2 + lam ≤ τε` from `lam ≤ τε/2`. -/
lemma h31_algebra (τ ε_inc lam : ℝ) (hlam : lam ≤ τ * ε_inc / 2) :
    τ * ε_inc / 2 + lam ≤ τ * ε_inc := by
  linarith

/-- Algebra helper: `-τε ≤ -(τε/2 + lam)` from `τε/2 + lam ≤ τε`. -/
lemma h37_algebra (τ ε_inc lam : ℝ) (h31 : τ * ε_inc / 2 + lam ≤ τ * ε_inc) :
    -τ * ε_inc ≤ -(τ * ε_inc / 2 + lam) := by
  have h : -(τ * ε_inc) ≤ -(τ * ε_inc / 2 + lam) := neg_le_neg h31
  have h2 : -τ * ε_inc = -(τ * ε_inc) := by ring
  rw [h2]
  exact h

/-- rpow comparison: `dk^(-τε) ≤ dm^(-ε)` from `dm ≤ dk^τ` and `0 < ε`. -/
lemma rpow_antitone_comparison (dk dm τ ε_inc : ℝ)
    (h_dk_pos : 0 < dk) (h_dm_pos : 0 < dm)
    (h_le : dm ≤ Real.rpow dk τ) (h_eps_pos : 0 < ε_inc) :
    Real.rpow dk (-τ * ε_inc) ≤ Real.rpow dm (-ε_inc) := by
  set dkτ := Real.rpow dk τ with hdkτ_def
  have h_pos_dkτ : 0 < dkτ := Real.rpow_pos_of_pos h_dk_pos τ
  have h1 : Real.rpow dm ε_inc ≤ Real.rpow dkτ ε_inc :=
    Real.rpow_le_rpow h_dm_pos.le h_le h_eps_pos.le
  have h2 : Real.rpow dm (-ε_inc) = (Real.rpow dm ε_inc)⁻¹ := by
    simpa using Real.rpow_neg h_dm_pos.le ε_inc
  have h3 : Real.rpow dkτ (-ε_inc) = (Real.rpow dkτ ε_inc)⁻¹ := by
    simpa using Real.rpow_neg h_pos_dkτ.le ε_inc
  have h_pos_dm_eps : 0 < Real.rpow dm ε_inc := Real.rpow_pos_of_pos h_dm_pos ε_inc
  have h4 : (Real.rpow dkτ ε_inc)⁻¹ ≤ (Real.rpow dm ε_inc)⁻¹ := by
    have h5 : 1 / Real.rpow dkτ ε_inc ≤ 1 / Real.rpow dm ε_inc :=
      one_div_le_one_div_of_le h_pos_dm_eps h1
    simpa using h5
  have h5 : Real.rpow dkτ (-ε_inc) ≤ Real.rpow dm (-ε_inc) := by
    rw [h3, h2]; exact h4
  have h6 : Real.rpow dkτ (-ε_inc) = Real.rpow dk (-τ * ε_inc) := by
    have h7 : Real.rpow dk (τ * (-ε_inc)) = Real.rpow dkτ (-ε_inc) :=
      Real.rpow_mul h_dk_pos.le τ (-ε_inc)
    have h8 : τ * (-ε_inc) = -τ * ε_inc := by ring
    rw [h8] at h7
    exact h7.symm
  rw [← h6]; exact h5

/-- rpow product helper: `dk^(-τε/2) * dk^(-lam) = dk^(-(τε/2 + lam))`. -/
lemma rpow_product_half_lam (dk : ℝ) (h_dk_pos : 0 < dk) (τ ε_inc lam : ℝ) :
    Real.rpow dk (-(τ * ε_inc / 2)) * Real.rpow dk (-lam) =
    Real.rpow dk (-(τ * ε_inc / 2 + lam)) := by
  have h := Real.rpow_add h_dk_pos (-(τ * ε_inc / 2)) (-lam)
  have h_sum : (-(τ * ε_inc / 2)) + (-lam) = -(τ * ε_inc / 2 + lam) := by ring
  rw [h_sum] at h
  exact h.symm

/-- Transfer a Finset.image card bound across DecidableEq instances. -/
lemma image_card_transfer {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) (K c : ℝ)
    (h : ((s.image f).card : ℝ) ≤ K * c) :
    ((@Finset.image α β (Classical.decEq β) f s).card : ℝ) ≤ K * c := by
  have h_ext : @Finset.image α β (Classical.decEq β) f s = s.image f := by
    ext x
    simp [Finset.mem_image]
  rw [h_ext]
  exact h

/-- Standalone wrapper for the good-case improved incidence argument.
    Extracts the lambda body from CIBW to avoid whnf timeouts. -/
lemma good_improved_incidence_wrapper
    (s t τ : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (n : ℕ) (h2 : 2 ≤ n) (k m : ℕ) (hk_ge_one : (1 : ℝ) ≤ (k : ℝ))
    (ε_G η lam ε_N C_P ε_inc : ℝ)
    (hεG : 0 < ε_G) (hτ : 0 < τ) (hη : 0 < η) (hεN : 0 < ε_N) (hCP : 1 ≤ C_P)
    (C_between : Fin n → ℝ)
    (Δ : Fin (n + 1) → ℝ)
    (scaleClass : Fin n → ScaleClass)
    (N : Fin n → ℕ)
    [DecidableEq (DyadicSquare m)]
    (M : ℕ)
    (config : CombiningTheorem.NiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (h_uniform : UniformIncidenceData s t ε_inc)
    (hextra : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass)
    (hm_eq2 : Δ 1 = dyadicDelta m)
    -- Absorption data
    (h6_abs : (9 * 2700 * 3145728 * (11 : ℝ)^7) * (k : ℝ)^(7 + C_P) < Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)))
    (hlam_le_τε_half : lam ≤ τ * ε_inc / 2)
    (hδm_leδR : dyadicDelta m ≤ h_uniform.δR)
    -- Lambda parameters
    (t_j : ℝ)
    (h_good_scale : scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j)
    (hnm : m ≤ k)
    (K' CΔ' : ℝ) (MΔ' : ℕ)
    (coarseConfig' : CombiningTheorem.NiceConfiguration m s CΔ' MΔ')
    (P' : Finset (DyadicSquare k))
    (hP_sub' : P' ⊆ config.P₀)
    (hcoarse_P_eq' : coarseConfig'.P₀ = P'.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound' : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K' * coarseConfig'.P₀.card)
    (hK_bound' : K' ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
    (hCΔ_bounds1' : CΔ' ≤ K' * Real.rpow (dyadicDelta k) (-lam))
    (hCΔ_bounds2' : Real.rpow (dyadicDelta k) (-lam) ≤ K' * CΔ')
    (h_slope_coarse' : ∀ T ∈ coarseConfig'.T₀, |T.slope| ≤ 1)
    (hP_nonempty' : P'.Nonempty) :
    (coarseConfig'.T₀.card : ENNReal) ≥
    ENNReal.ofReal (Real.rpow (dyadicDelta m) (-(2 * s + ε_inc))) := by
  classical
  set C_absorb2_const : ℝ := 9 * 2700 * 3145728 * (11 : ℝ)^7 with hC_def
  let δR := h_uniform.δR
  let hδR_pos := h_uniform.hδR_pos
  let h_body_all := h_uniform.h_body
  let h_est_body := h_body_all m
  let i0 : Fin n := ⟨0, by omega⟩
  let C_between0 := C_between i0
  have hC_between0_pos : 0 < C_between0 := by
    have h_good_reg := hcfg.h_good i0 t_j h_good_scale
    exact h_good_reg.2.1
  let K'' := max K' (1 / (9 * C_between0))
  have hK''_ge_K' : K'' ≥ K' := le_max_left _ _
  have hC_ge1 : 1 ≤ 9 * K'' * C_between0 := by
    dsimp only [K'']
    by_cases h : K' ≥ 1 / (9 * C_between0)
    · rw [max_eq_left h]
      have h9 : 0 < 9 * C_between0 := by positivity
      have h10 : 1 ≤ 9 * C_between0 * K' := by
        calc 1 = 9 * C_between0 * (1 / (9 * C_between0)) := by field_simp [h9.ne'] <;> ring
          _ ≤ 9 * C_between0 * K' := by gcongr
      linarith
    · have h11 : K' ≤ 1 / (9 * C_between0) := le_of_not_ge h
      rw [max_eq_right h11]
      have h9 : 0 < 9 * C_between0 := by positivity
      have h10 : 9 * (1 / (9 * C_between0)) * C_between0 = 1 := by
        field_simp [h9.ne'] <;> ring
      rw [h10] <;> norm_num
  have h_card_bound'' : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K'' * coarseConfig'.P₀.card := by
    calc (config.P₀.image (InductionConfigurations.containingSquare hnm)).card
      ≤ K' * coarseConfig'.P₀.card := h_card_bound'
    _ ≤ K'' * coarseConfig'.P₀.card := by
      have h : (K' : ℝ) * (coarseConfig'.P₀.card : ℝ) ≤ (K'' : ℝ) * (coarseConfig'.P₀.card : ℝ) :=
        mul_le_mul_of_nonneg_right hK''_ge_K' (Nat.cast_nonneg _)
      exact_mod_cast h
  have h_good_reg : IsRegularBetweenScales config.pointSet (dyadicDelta m) 1 t_j C_between0 C_between0 := by
    have h := hcfg.h_good i0 t_j h_good_scale
    have h9 : Δ (Fin.succ i0) = dyadicDelta m := by
      have h10 : (Fin.succ i0) = (1 : Fin (n + 1)) := by
        apply Fin.ext
        have h_lt : 1 < n + 1 := by linarith [h2]
        have h_mod : (1 : ℕ) % (n + 1) = 1 := Nat.mod_eq_of_lt h_lt
        have h_i0_val : i0.val = 0 := by simp [i0]
        rw [Fin.val_succ, h_i0_val]
        <;> simp [h_mod]
        <;> rfl
      rw [h10]
      exact hm_eq2
    have h11 : Δ (Fin.castSucc i0) = (1 : ℝ) := by
      have h12 : (Fin.castSucc i0) = (0 : Fin (n + 1)) := by
        apply Fin.ext
        simp [i0]
      rw [h12]
      exact hcfg.hΔ_start
    have h' : IsRegularBetweenScales config.pointSet (dyadicDelta m) 1 t_j C_between0 C_between0 := by
      rw [h9, h11] at h
      exact h
    exact h'
  have hu_t : t ≤ t_j := hextra.h_tj_ge_t i0 t_j h_good_scale
  have htj_two : t_j ≤ 2 := hextra.h_tj_le_two i0 t_j h_good_scale
  have hnotbad : ¬(scaleClass i0).isBad := by
    rw [h_good_scale] <;> simp [ScaleClass.isBad] <;> trivial
  have h_scale0 := hcfg.h_scale_ratio i0 hnotbad
  have hΔ0_abs : Δ 0 = 1 := hcfg.hΔ_start
  have hΔ1_abs : Δ 1 = dyadicDelta m := hm_eq2
  have h_scale_ratio0 : Δ 1 / Δ 0 ≤ Real.rpow (dyadicDelta k) τ :=
    Prop73Restructure.first_scale_ratio (by linarith) Δ (Real.rpow (dyadicDelta k) τ) h_scale0
  have h_scale_ratio1 : dyadicDelta m ≤ Real.rpow (dyadicDelta k) τ := by
    simpa [div_one, hΔ0_abs, hΔ1_abs] using h_scale_ratio0
  have hm_geτk : (m : ℝ) ≥ τ * (k : ℝ) :=
    scale_ratio_to_ge hτ h_scale_ratio1
  have hδm_le_δkτ : dyadicDelta m ≤ Real.rpow (dyadicDelta k) τ := by
    have h9 : dyadicDelta m = Real.rpow 2 (-(m : ℝ)) := by simp [dyadicDelta] <;> norm_cast
    have h10 : Real.rpow (dyadicDelta k) τ = Real.rpow 2 (-(τ * (k : ℝ))) := by
      have h11 : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by simp [dyadicDelta] <;> norm_cast
      have h12 : Real.rpow (Real.rpow 2 (-(k : ℝ))) τ = Real.rpow 2 ((-(k : ℝ)) * τ) :=
        (Real.rpow_mul (by norm_num) (-(k : ℝ)) τ).symm
      calc Real.rpow (dyadicDelta k) τ
        = Real.rpow (Real.rpow 2 (-(k : ℝ))) τ := by rw [h11]
      _ = Real.rpow 2 ((-(k : ℝ)) * τ) := h12
      _ = Real.rpow 2 (-(τ * (k : ℝ))) := by ring_nf
    rw [h9, h10]
    have h13 : -(m : ℝ) ≤ -(τ * (k : ℝ)) := by linarith [hm_geτk]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h13
  have hratio_ge1 : (1 - s) / (min t 1 - s) ≥ 1 := by
    have h1 : min t 1 ≤ 1 := min_le_right _ _
    have h2 : 0 < min t 1 - s := by have h3 : s < min t 1 := lt_min hst hs1; linarith
    have h4 : min t 1 - s ≤ 1 - s := by linarith
    exact one_le_div h2 |>.mpr h4
  have hεG_le_half : ε_G ≤ ε_inc / 2 := by
    have h_exp : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc := hextra.h_exp_condition
    have hη_nonneg : 0 ≤ η := by linarith [hη]
    have h5 : (η + 2 * ε_G) * ((1 - s) / (min t 1 - s)) ≤ ε_inc := by
      have h_eq : (η + 2 * ε_G) * ((1 - s) / (min t 1 - s)) = (η + 2 * ε_G) * (1 - s) / (min t 1 - s) := by ring
      rw [h_eq]
      linarith
    have h6 : 2 * ε_G ≤ (η + 2 * ε_G) * ((1 - s) / (min t 1 - s)) := by
      have h7 : 0 ≤ η + 2 * ε_G := by linarith [hη, hεG]
      have h8 : (η + 2 * ε_G) * 1 ≤ (η + 2 * ε_G) * ((1 - s) / (min t 1 - s)) :=
        mul_le_mul_of_nonneg_left hratio_ge1 h7
      have h9 : (η + 2 * ε_G) * 1 = η + 2 * ε_G := by ring
      rw [h9] at h8
      linarith
    linarith
  have hdk_lt_one : dyadicDelta k < 1 := by
    have h15 : (k : ℝ) ≥ 1 := hk_ge_one
    have hk_nat : 1 ≤ k := by exact_mod_cast hk_ge_one
    have h16 : dyadicDelta k ≤ dyadicDelta 1 := dyadicDelta_anti hk_nat
    have h17 : dyadicDelta 1 = 1 / 2 := by simp [dyadicDelta] <;> norm_num
    rw [h17] at h16
    linarith
  have h_exp_compare : Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) ≤ Real.rpow (dyadicDelta m) (-ε_inc) := by
    have h11 : Real.rpow (dyadicDelta m) (-ε_inc) ≥ Real.rpow (Real.rpow (dyadicDelta k) τ) (-ε_inc) := by
      have h_pos1 : 0 < dyadicDelta m := dyadicDelta_pos m
      have h_pos2 : 0 < Real.rpow (dyadicDelta k) τ := Real.rpow_pos_of_pos (dyadicDelta_pos k) _
      have h_le : dyadicDelta m ≤ Real.rpow (dyadicDelta k) τ := hδm_le_δkτ
      have h_pos_exp : 0 ≤ ε_inc := by linarith [hextra.hε_inc_pos]
      have h1 : Real.rpow (dyadicDelta m) ε_inc ≤ Real.rpow (Real.rpow (dyadicDelta k) τ) ε_inc :=
        Real.rpow_le_rpow (by linarith) h_le h_pos_exp
      have h2 : Real.rpow (dyadicDelta m) (-ε_inc) = (Real.rpow (dyadicDelta m) ε_inc)⁻¹ := by
        simpa using Real.rpow_neg h_pos1.le ε_inc
      have h3 : Real.rpow (Real.rpow (dyadicDelta k) τ) (-ε_inc) = (Real.rpow (Real.rpow (dyadicDelta k) τ) ε_inc)⁻¹ := by
        simpa using Real.rpow_neg h_pos2.le ε_inc
      rw [h2, h3]
      have h_pos1' : 0 < Real.rpow (dyadicDelta m) ε_inc := Real.rpow_pos_of_pos h_pos1 _
      have h4 : 1 / Real.rpow (Real.rpow (dyadicDelta k) τ) ε_inc ≤ 1 / Real.rpow (dyadicDelta m) ε_inc :=
        one_div_le_one_div_of_le h_pos1' h1
      have h5 : (Real.rpow (Real.rpow (dyadicDelta k) τ) ε_inc)⁻¹ ≤ (Real.rpow (dyadicDelta m) ε_inc)⁻¹ := by
        have h6 : ∀ (x : ℝ), 1 / x = x⁻¹ := by intro x; ring
        rw [h6 _, h6 _] at h4
        exact h4
      exact h5
    have h12 : Real.rpow (Real.rpow (dyadicDelta k) τ) (-ε_inc) = Real.rpow (dyadicDelta k) (-τ * ε_inc) := by
      have h12a : Real.rpow (Real.rpow (dyadicDelta k) τ) (-ε_inc) = Real.rpow (dyadicDelta k) (τ * (-ε_inc)) :=
        (Real.rpow_mul (dyadicDelta_pos k).le τ (-ε_inc)).symm
      rw [h12a]
      <;> ring_nf
    rw [h12] at h11
    have h13 : Real.rpow (dyadicDelta k) (-τ * ε_inc) ≥ Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) := by
      have h18 : -τ * ε_inc ≤ -(τ * ε_inc / 2) := by
        have h_pos : 0 < τ * ε_inc := mul_pos hτ hextra.hε_inc_pos
        nlinarith
      have h19 : 0 < dyadicDelta k := dyadicDelta_pos k
      have h20 : dyadicDelta k ≤ 1 := dyadicDelta_le_one k
      exact Real.rpow_le_rpow_of_exponent_ge h19 h20 h18
    exact le_trans h13 h11
  have h_key_compare : Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) ≤ Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) := by
    have h_exp1 : Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) = Real.rpow 2 ((k : ℝ) * (τ * ε_inc / 2)) := by
      have hdk : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by simp [dyadicDelta] <;> norm_cast
      have h : Real.rpow (Real.rpow 2 (-(k : ℝ))) (-(τ * ε_inc / 2)) = Real.rpow 2 ((-(k : ℝ)) * (-(τ * ε_inc / 2))) :=
        (Real.rpow_mul (by norm_num) (-(k : ℝ)) (-(τ * ε_inc / 2))).symm
      rw [hdk, h] <;> ring_nf
    have h_exp2 : Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) = Real.rpow 2 ((m : ℝ) * (ε_inc - ε_G)) := by
      have hdm : dyadicDelta m = Real.rpow 2 (-(m : ℝ)) := by simp [dyadicDelta] <;> norm_cast
      have h : Real.rpow (Real.rpow 2 (-(m : ℝ))) (-(ε_inc - ε_G)) = Real.rpow 2 ((-(m : ℝ)) * (-(ε_inc - ε_G))) :=
        (Real.rpow_mul (by norm_num) (-(m : ℝ)) (-(ε_inc - ε_G))).symm
      rw [hdm, h] <;> ring_nf
    rw [h_exp1, h_exp2]
    have h_ineq : (k : ℝ) * (τ * ε_inc / 2) ≤ (m : ℝ) * (ε_inc - ε_G) := by
      have h1 : (m : ℝ) ≥ τ * (k : ℝ) := hm_geτk
      have h2 : ε_inc - ε_G ≥ ε_inc / 2 := by linarith [hεG_le_half, hextra.hε_inc_pos]
      have h3 : 0 ≤ (k : ℝ) := by linarith [hk_ge_one]
      have h4 : 0 ≤ ε_inc - ε_G := by linarith [hεG_le_half, hextra.hε_inc_pos]
      calc (k : ℝ) * (τ * ε_inc / 2)
        = τ * (k : ℝ) * (ε_inc / 2) := by ring
      _ ≤ (m : ℝ) * (ε_inc / 2) := by gcongr <;> linarith
      _ ≤ (m : ℝ) * (ε_inc - ε_G) := by gcongr <;> linarith
    have h_pos : 1 ≤ (2 : ℝ) := by norm_num
    exact Real.rpow_le_rpow_of_exponent_le h_pos h_ineq
  have hCb_good : C_between0 ≤ Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G := by
    have h := hcfg.h_C_between_good i0 t_j h_good_scale
    have h9 : Δ (Fin.succ i0) = dyadicDelta m := by
      have h10 : (Fin.succ i0) = (1 : Fin (n + 1)) := by
        apply Fin.ext
        have h_lt : 1 < n + 1 := by linarith [h2]
        have h_mod : (1 : ℕ) % (n + 1) = 1 := Nat.mod_eq_of_lt h_lt
        have h_i0_val : i0.val = 0 := by simp [i0]
        rw [Fin.val_succ, h_i0_val]
        <;> simp [h_mod]
        <;> rfl
      rw [h10]; exact hm_eq2
    have h11 : Δ (Fin.castSucc i0) = (1 : ℝ) := by
      have h12 : (Fin.castSucc i0) = (0 : Fin (n + 1)) := by
        apply Fin.ext
        simp [i0]
      rw [h12]; exact hcfg.hΔ_start
    have h' : C_between0 ≤ Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G := by
      rw [h9, h11] at h
      exact h
    exact h'
  have hlog_eq : Real.log (1 / dyadicDelta k) = (k : ℝ) * Real.log 2 := by
    have h4 : 1 / dyadicDelta k = Real.rpow 2 (k : ℝ) := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h4]; simpa using Real.log_rpow (by norm_num) (k : ℝ)
  have hCP_nonneg : 0 ≤ C_P := by linarith [hCP]
  have h1_log : Real.log (1 / dyadicDelta k) ^ C_P ≤ (k : ℝ)^C_P := by
    rw [hlog_eq]
    have h3 := Prop73Restructure.index_log_two_le k
    have h4 : 0 ≤ (k : ℝ) * Real.log 2 := by positivity
    gcongr <;> linarith
  have h9_rpow : Real.rpow (1 / dyadicDelta m) ε_G = Real.rpow (dyadicDelta m) (-ε_G) := by
    have h1 : 1 / dyadicDelta m = (dyadicDelta m)⁻¹ := by ring
    rw [h1]
    exact (Real.rpow_neg_eq_inv_rpow (dyadicDelta m) ε_G).symm
  have hC_weaken2 : C_between0 ≤ Real.rpow (dyadicDelta m) (-ε_inc) := by
    have h10 : Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) ≤ Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) := h_key_compare
    have h_pos_epsG : 0 ≤ Real.rpow (dyadicDelta m) (-ε_G) := Real.rpow_nonneg (dyadicDelta_pos m).le _
    have h_k1 : 1 ≤ (k : ℝ) := hk_ge_one
    have h_CP_nonneg : 0 ≤ C_P := by linarith [hCP]
    have h_kCP_le_k7CP : (k : ℝ)^C_P ≤ (k : ℝ)^(7 + C_P) := by gcongr <;> linarith
    have h_main : C_between0 < Real.rpow (dyadicDelta m) (-ε_inc) := by
      calc C_between0
        ≤ Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G := hCb_good
      _ ≤ (k : ℝ)^C_P * Real.rpow (dyadicDelta m) (-ε_G) := by
        rw [h9_rpow]
        exact mul_le_mul_of_nonneg_right h1_log h_pos_epsG
      _ ≤ (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta m) (-ε_G) := by
        exact mul_le_mul_of_nonneg_right h_kCP_le_k7CP h_pos_epsG
      _ ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta m) (-ε_G) := by
        have h_k_nonneg : 0 ≤ (k : ℝ)^(7 + C_P) := by positivity
        have h : (k : ℝ)^(7 + C_P) ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) := by
          have h_C_ge1 : 1 ≤ C_absorb2_const := by rw [hC_def] <;> norm_num
          calc (k : ℝ)^(7 + C_P)
            = 1 * (k : ℝ)^(7 + C_P) := by ring
          _ ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) := by gcongr
        exact mul_le_mul_of_nonneg_right h h_pos_epsG
      _ < Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) * Real.rpow (dyadicDelta m) (-ε_G) := by
        have h_pos_epsG' : 0 < Real.rpow (dyadicDelta m) (-ε_G) := Real.rpow_pos_of_pos (dyadicDelta_pos m) _
        exact mul_lt_mul_of_pos_right h6_abs h_pos_epsG'
      _ ≤ Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) * Real.rpow (dyadicDelta m) (-ε_G) := by
        exact mul_le_mul_of_nonneg_right h10 h_pos_epsG
      _ = Real.rpow (dyadicDelta m) (-ε_inc) := by
        have h_add : Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) * Real.rpow (dyadicDelta m) (-ε_G) =
            Real.rpow (dyadicDelta m) ((-(ε_inc - ε_G)) + (-ε_G)) :=
          (Real.rpow_add (dyadicDelta_pos m) (-(ε_inc - ε_G)) (-ε_G)).symm
        rw [h_add]
        have h_sum : (-(ε_inc - ε_G)) + (-ε_G) = -ε_inc := by ring
        rw [h_sum]
    exact h_main.le
  have hC_weaken1 : 9 * K'' * C_between0 ≤ Real.rpow (dyadicDelta m) (-ε_inc) := by
    have hpos : 0 < 9 * C_between0 := by positivity
    by_cases hcase : 9 * K' * C_between0 ≤ 1
    · have h10 : 9 * K'' * C_between0 = 1 := by
        dsimp only [K'']
        have h11 : K' ≤ 1 / (9 * C_between0) := by
          have h : 9 * C_between0 * K' ≤ 1 := by linarith
          calc K'
            = (9 * C_between0 * K') / (9 * C_between0) := by field_simp [hpos.ne'] <;> ring
          _ ≤ 1 / (9 * C_between0) := by gcongr
        rw [max_eq_right h11]
        have h12 : 9 * (1 / (9 * C_between0)) * C_between0 = 1 := by
          field_simp [hpos.ne'] <;> ring
        rw [h12] <;> ring
      rw [h10]
      have h13 : (1 : ℝ) ≤ Real.rpow (dyadicDelta m) (-ε_inc) := by
        have h14 : dyadicDelta m ≤ 1 := dyadicDelta_le_one m
        have h15 : -ε_inc ≤ 0 := by linarith [hextra.hε_inc_pos]
        exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (dyadicDelta_pos m) h14 h15
      exact h13
    · have h10 : 9 * K' * C_between0 > 1 := by linarith
      have h11 : 9 * K'' * C_between0 = 9 * K' * C_between0 := by
        dsimp only [K'']
        have h12 : K' ≥ 1 / (9 * C_between0) := by
          have h : 9 * C_between0 * K' > 1 := by linarith
          have h' : K' > 1 / (9 * C_between0) := by
            calc K'
              = (9 * C_between0 * K') / (9 * C_between0) := by field_simp [hpos.ne'] <;> ring
            _ > 1 / (9 * C_between0) := by gcongr
          exact h'.le
        rw [max_eq_left h12] <;> ring
      rw [h11]
      have h_pos_epsG : 0 ≤ Real.rpow (dyadicDelta m) (-ε_G) := Real.rpow_nonneg (dyadicDelta_pos m).le _
      have h14 : K' ≤ (2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7 := by
        have h_k1 : 1 ≤ (k : ℝ) := hk_ge_one
        have h_ineq : 4 * (k : ℝ) + 7 ≤ 11 * (k : ℝ) := by linarith
        have h_pow : (4 * (k : ℝ) + 7)^7 ≤ (11 * (k : ℝ))^7 := by
          gcongr
        calc K'
          ≤ (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 := hK_bound'
        _ ≤ (2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7 := by gcongr
      have h15 : 9 * K' * C_between0 ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta m) (-ε_G) := by
        have hP_coarse_nonempty : coarseConfig'.P₀.Nonempty := by
          rw [hcoarse_P_eq']
          exact Finset.Nonempty.image hP_nonempty' _
        have h_card_pos : 0 < (coarseConfig'.P₀.card : ℝ) := by
          exact_mod_cast Finset.Nonempty.card_pos hP_coarse_nonempty
        have hK'_nonneg : 0 ≤ K' := by
          by_contra hK_neg
          have hK_neg' : K' < 0 := by linarith
          have h_prod_neg : K' * (coarseConfig'.P₀.card : ℝ) < 0 :=
            mul_neg_of_neg_of_pos hK_neg' h_card_pos
          have h_bound : ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤ K' * (coarseConfig'.P₀.card : ℝ) := by
            simpa using h_card_bound'
          have h_nonneg : 0 ≤ ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) := by positivity
          linarith
        have hCb_nonneg : 0 ≤ C_between0 := hC_between0_pos.le
        have h_big_nonneg : 0 ≤ (2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7 := by positivity
        have h_log_pos : 0 < Real.log (1 / dyadicDelta k) := by
          have h1 : 1 < 1 / dyadicDelta k := by
            have h2 : 0 < dyadicDelta k := dyadicDelta_pos k
            have h3 : dyadicDelta k < 1 := hdk_lt_one
            exact one_lt_one_div h2 h3
          exact Real.log_pos h1
        have h_log_rpow_nonneg : 0 ≤ Real.log (1 / dyadicDelta k) ^ C_P :=
          Real.rpow_nonneg h_log_pos.le C_P
        have h1 : K' * C_between0 ≤ ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * (Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G) :=
          mul_le_mul h14 hCb_good hCb_nonneg h_big_nonneg
        have h_k_pos : 0 < (k : ℝ) := by linarith [hk_ge_one]
        have h_k_mul : (k : ℝ)^7 * (k : ℝ)^C_P = (k : ℝ)^(7 + C_P) := by
          have h4 : Real.rpow (k : ℝ) (7 : ℝ) = (k : ℝ)^7 := Real.rpow_natCast (k : ℝ) 7
          have h5 : (k : ℝ)^7 = Real.rpow (k : ℝ) (7 : ℝ) := h4.symm
          rw [h5]
          exact (Real.rpow_add h_k_pos (7 : ℝ) C_P).symm
        have h_big_eq : (2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7 = (2700 * 3145728 * 11^7 : ℝ) * (k : ℝ)^7 := by ring
        have h_step1 : 9 * K' * C_between0 ≤ 9 * (((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * (Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G)) := by
          have h_expand : 9 * K' * C_between0 = 9 * (K' * C_between0) := by ring
          rw [h_expand]
          exact mul_le_mul_of_nonneg_left h1 (by norm_num)
        have h6 : Real.rpow (1 / dyadicDelta m) ε_G = Real.rpow (dyadicDelta m) (-ε_G) := h9_rpow
        have h7 : Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G ≤ (k : ℝ)^C_P * Real.rpow (dyadicDelta m) (-ε_G) := by
          rw [h6]
          exact mul_le_mul_of_nonneg_right h1_log (Real.rpow_nonneg (dyadicDelta_pos m).le _)
        have h_big_pos2 : 0 ≤ 9 * ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) := by positivity
        have h_step2 : 9 * ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * (Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G) ≤
            9 * ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * ((k : ℝ)^C_P * Real.rpow (dyadicDelta m) (-ε_G)) := by
          exact mul_le_mul_of_nonneg_left h7 h_big_pos2
        have h_step3 : 9 * ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * ((k : ℝ)^C_P * Real.rpow (dyadicDelta m) (-ε_G)) =
            C_absorb2_const * (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta m) (-ε_G) := by
          have h9 : 9 * ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * ((k : ℝ)^C_P * Real.rpow (dyadicDelta m) (-ε_G)) =
              (9 * (2700 * 3145728 * 11^7 : ℝ)) * ((k : ℝ)^7 * (k : ℝ)^C_P) * Real.rpow (dyadicDelta m) (-ε_G) := by
            rw [h_big_eq] <;> ring
          rw [h9]
          have h10 : (9 * (2700 * 3145728 * 11^7 : ℝ)) * ((k : ℝ)^7 * (k : ℝ)^C_P) * Real.rpow (dyadicDelta m) (-ε_G) =
              C_absorb2_const * ((k : ℝ)^7 * (k : ℝ)^C_P) * Real.rpow (dyadicDelta m) (-ε_G) := by
            rw [hC_def] <;> ring
          rw [h10, h_k_mul] <;> ring
        have h_final : 9 * K' * C_between0 ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta m) (-ε_G) := by
          calc 9 * K' * C_between0
            = 9 * (K' * C_between0) := by ring
          _ ≤ 9 * (((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * (Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G)) := by
            exact mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ = 9 * ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * (Real.log (1 / dyadicDelta k) ^ C_P * Real.rpow (1 / dyadicDelta m) ε_G) := by ring
          _ ≤ 9 * ((2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7) * ((k : ℝ)^C_P * Real.rpow (dyadicDelta m) (-ε_G)) := h_step2
          _ = C_absorb2_const * (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta m) (-ε_G) := h_step3
        exact h_final
      have h18 : C_absorb2_const * (k : ℝ)^(7 + C_P) < Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) := by
        rw [hC_def] at *; exact h6_abs
      have h19 : Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) ≤ Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) := h_key_compare
      have h_main : 9 * K' * C_between0 < Real.rpow (dyadicDelta m) (-ε_inc) := by
        calc 9 * K' * C_between0
          ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta m) (-ε_G) := h15
        _ < Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) * Real.rpow (dyadicDelta m) (-ε_G) := by
          have h_pos_epsG' : 0 < Real.rpow (dyadicDelta m) (-ε_G) := Real.rpow_pos_of_pos (dyadicDelta_pos m) _
          exact mul_lt_mul_of_pos_right h18 h_pos_epsG'
        _ ≤ Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) * Real.rpow (dyadicDelta m) (-ε_G) := by
          exact mul_le_mul_of_nonneg_right h19 h_pos_epsG
        _ = Real.rpow (dyadicDelta m) (-ε_inc) := by
          have h_add : Real.rpow (dyadicDelta m) (-(ε_inc - ε_G)) * Real.rpow (dyadicDelta m) (-ε_G) =
              Real.rpow (dyadicDelta m) ((-(ε_inc - ε_G)) + (-ε_G)) :=
            (Real.rpow_add (dyadicDelta_pos m) (-(ε_inc - ε_G)) (-ε_G)).symm
          rw [h_add]
          have h_sum : (-(ε_inc - ε_G)) + (-ε_G) = -ε_inc := by ring
          rw [h_sum]
      exact h_main.le
  have hCΔ_weaken : CΔ' ≤ Real.rpow (dyadicDelta m) (-ε_inc) := by
    have h22 : CΔ' ≤ K' * Real.rpow (dyadicDelta k) (-lam) := hCΔ_bounds1'
    have h29 : K' ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) := by
      have h_k1 : 1 ≤ (k : ℝ) := hk_ge_one
      have h_CP_nonneg : 0 ≤ C_P := by linarith [hCP]
      have h_k7 : (k : ℝ)^7 ≤ (k : ℝ)^(7 + C_P) := by
        have h4 : Real.rpow (k : ℝ) (7 : ℝ) = (k : ℝ)^7 := Real.rpow_natCast (k : ℝ) 7
        have h5 : (k : ℝ)^7 = Real.rpow (k : ℝ) (7 : ℝ) := h4.symm
        rw [h5]
        have h6 : (7 : ℝ) ≤ (7 + C_P : ℝ) := by linarith [hCP]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [hk_ge_one]) h6
      have h_pos_k : 0 ≤ (k : ℝ)^(7 + C_P) := by positivity
      calc K'
        ≤ (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 := hK_bound'
      _ ≤ (2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7 := by gcongr <;> linarith
      _ = (2700 * 3145728 * 11^7 : ℝ) * (k : ℝ)^7 := by ring
      _ ≤ (2700 * 3145728 * 11^7 : ℝ) * (k : ℝ)^(7 + C_P) := by
        exact mul_le_mul_of_nonneg_left h_k7 (by norm_num)
      _ ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) := by
        have h_c : (2700 * 3145728 * 11^7 : ℝ) ≤ C_absorb2_const := by
          rw [hC_def] <;> norm_num
        have h_k_nonneg : 0 ≤ (k : ℝ)^(7 + C_P) := by positivity
        exact mul_le_mul_of_nonneg_right h_c h_k_nonneg
    have h30 : C_absorb2_const * (k : ℝ)^(7 + C_P) < Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) := by
      rw [hC_def] at *; exact h6_abs
    have h31 : τ * ε_inc / 2 + lam ≤ τ * ε_inc :=
      h31_algebra τ ε_inc lam hlam_le_τε_half
    have h37 : -τ * ε_inc ≤ -(τ * ε_inc / 2 + lam) :=
      h37_algebra τ ε_inc lam h31
    have h32 : Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2 + lam)) ≤ Real.rpow (dyadicDelta k) (-τ * ε_inc) :=
      Real.rpow_le_rpow_of_exponent_ge (dyadicDelta_pos k) (dyadicDelta_le_one k) h37
    have h33 : Real.rpow (dyadicDelta k) (-τ * ε_inc) ≤ Real.rpow (dyadicDelta m) (-ε_inc) :=
      rpow_antitone_comparison (dyadicDelta k) (dyadicDelta m) τ ε_inc
        (dyadicDelta_pos k) (dyadicDelta_pos m) hδm_le_δkτ hextra.hε_inc_pos
    have hCΔ_weaken : CΔ' ≤ Real.rpow (dyadicDelta m) (-ε_inc) := by
      calc CΔ'
        ≤ K' * Real.rpow (dyadicDelta k) (-lam) := h22
      _ ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) * Real.rpow (dyadicDelta k) (-lam) := by
        have h_pos2 : 0 ≤ Real.rpow (dyadicDelta k) (-lam) := Real.rpow_nonneg (dyadicDelta_pos k).le _
        exact mul_le_mul_of_nonneg_right h29 h_pos2
      _ ≤ Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) * Real.rpow (dyadicDelta k) (-lam) := by
        have h_pos : 0 < Real.rpow (dyadicDelta k) (-lam) := Real.rpow_pos_of_pos (dyadicDelta_pos k) _
        exact mul_le_mul_of_nonneg_right (le_of_lt h30) h_pos.le
      _ = Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2 + lam)) :=
        rpow_product_half_lam (dyadicDelta k) (dyadicDelta_pos k) τ ε_inc lam
      _ ≤ Real.rpow (dyadicDelta k) (-τ * ε_inc) := h32
      _ ≤ Real.rpow (dyadicDelta m) (-ε_inc) := h33
    exact hCΔ_weaken
  have hδ_le_R : dyadicDelta m ≤ δR := hδm_leδR
  have hcoarse_P_eq_final : coarseConfig'.P₀ =
      @Finset.image (DyadicSquare k) (DyadicSquare m) (Classical.decEq (DyadicSquare m))
        (InductionConfigurations.containingSquare hnm) P' := by
    apply Finset.ext
    intro x
    have h1 : x ∈ coarseConfig'.P₀ ↔ ∃ y ∈ P', InductionConfigurations.containingSquare hnm y = x := by
      rw [hcoarse_P_eq']
      simp [Finset.mem_image]
      <;> rfl
    have h2 : x ∈ @Finset.image (DyadicSquare k) (DyadicSquare m) (Classical.decEq (DyadicSquare m))
          (InductionConfigurations.containingSquare hnm) P' ↔
        ∃ y ∈ P', InductionConfigurations.containingSquare hnm y = x := by
      simp [Finset.mem_image]
      <;> rfl
    rw [h1, h2]
  have h_card_bound_final : ((@Finset.image (DyadicSquare k) (DyadicSquare m) (Classical.decEq (DyadicSquare m))
      (InductionConfigurations.containingSquare hnm) config.P₀).card : ℝ) ≤
      K'' * (coarseConfig'.P₀.card : ℝ) :=
    image_card_transfer config.P₀ (InductionConfigurations.containingSquare hnm) K''
      (coarseConfig'.P₀.card : ℝ) h_card_bound''
  exact good_case_improved_incidence
    (εReg := ε_inc) (η := ε_inc) (K := K'') (C_between := C_between0) (CΔ := CΔ')
    (hnm := hnm) (config := config) (coarseConfig := coarseConfig')
    (P := P') (hP_sub := hP_sub') (hcoarse_P_eq := hcoarse_P_eq_final)
    (h_card_bound := h_card_bound_final) (hP_nonempty := hP_nonempty')
    (h_squares_unit := hB1.h_squares_unit) (h_good := h_good_reg)
    (h_slope_coarse := h_slope_coarse')
    (h_est_body := h_est_body hδ_le_R)
    (hu_t := hu_t) (htj_two := htj_two) (hs1 := hs1) (hst := hst)
    (hK_pos := by positivity) (hC_between_pos := hC_between0_pos)
    (hC_ge1 := hC_ge1) (hC_weaken1 := hC_weaken1)
    (hC_weaken2 := hC_weaken2) (hCΔ_weaken := hCΔ_weaken)
    (hεReg_pos := hextra.hε_inc_pos) (hη_pos := hextra.hε_inc_pos)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
