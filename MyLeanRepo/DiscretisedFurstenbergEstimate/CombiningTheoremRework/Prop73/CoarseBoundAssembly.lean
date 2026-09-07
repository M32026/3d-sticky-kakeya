module

/-
  Coarse Bound Assembly — Standalone extraction of the first-scale coarse bound.

  Wraps the case split on the first scale class (bad / normal / good) and
  dispatches to the appropriate helper lemma. Extracted from
  InductiveStepCore_v2.lean to avoid tactic timeouts in the huge proof context
  containing ~30 Classical.choose bindings.

  Whiteprint node: combining_theorem_genuine / inductive_step_core_v2
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundDispatcher
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NormalCoarseBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCoarseBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCaseImprovedIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DirecretisedFurstenbergEstimate.RegularIncidence

local instance {n : ℕ} : DecidableEq (DyadicSquare n) := Classical.decEq (DyadicSquare n)

/-- Helper: if 2 ≤ m, then 1 ≤ Real.log (1 / dyadicDelta m). -/
lemma assembly_dyadicDelta_log_ge_one {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ Real.log (1 / dyadicDelta m) := by
  have h1 : dyadicDelta m ≤ 1 / 4 := by
    dsimp only [dyadicDelta]
    have h2 : (2 : ℝ)^2 ≤ (2 : ℝ)^m := pow_le_pow_right₀ (by norm_num) hm
    have h3 : 0 < (2 : ℝ)^2 := by positivity
    have h4 : 1 / (2 : ℝ)^m ≤ 1 / (2 : ℝ)^2 := one_div_le_one_div_of_le h3 h2
    have h5 : 1 / (2 : ℝ)^2 = 1 / 4 := by norm_num
    rw [h5] at h4; exact h4
  have h3 : 4 ≤ 1 / dyadicDelta m := by
    have h4 : 1 / dyadicDelta m ≥ 1 / (1 / 4) := one_div_le_one_div_of_le (dyadicDelta_pos m) h1
    have h5 : 1 / (1 / 4 : ℝ) = 4 := by norm_num
    rw [h5] at h4; exact h4
  have h4 : Real.log 4 ≤ Real.log (1 / dyadicDelta m) := Real.log_le_log (by norm_num) h3
  have h5 : (1 : ℝ) < Real.log 4 := by
    have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_three]
    have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
    have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    rw [h8] at h7; exact h7
  linarith

/-- m=1 bad first-scale bound: C_coarse=0, all non-MΔ factors ≤ 1. -/
lemma assembly_coarse_bound_m1_bad
    {Δ_coarse δ K C'_coarse C_coarse MΔ PΔ : ℝ} {TΔ_card : ℝ}
    (s ε_N lam : ℝ)
    (hΔ_pos : 0 < Δ_coarse) (hΔ_lt_one : Δ_coarse < 1)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hK_ge1 : 1 ≤ K)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hlam : 0 < lam)
    (hs : 0 < s) (hs1 : s < 1) (hεN : 0 < ε_N)
    (hC0 : C_coarse = 0)
    (hPΔ : PΔ = Δ_coarse)
    (hTΔ_ge : TΔ_card ≥ MΔ)
    (hMΔ_nonneg : 0 ≤ MΔ) :
    TΔ_card ≥ Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * MΔ *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
  have h1 : Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) = 1 := by
    have hC0' : -C_coarse = 0 := by linarith [hC0]
    rw [hC0']; simp
  have h2 : Real.rpow Δ_coarse (-s + ε_N) * PΔ = Real.rpow Δ_coarse (-s + ε_N + 1) := by
    rw [hPΔ]
    have h_rpow1 : Real.rpow Δ_coarse 1 = Δ_coarse := by simp
    have h_add : Real.rpow Δ_coarse ((-s + ε_N) + 1) =
        Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse 1 :=
      Real.rpow_add hΔ_pos (-s + ε_N) 1
    have h4 : Real.rpow Δ_coarse (-s + ε_N) * Δ_coarse = Real.rpow Δ_coarse (-s + ε_N + 1) := by
      calc Real.rpow Δ_coarse (-s + ε_N) * Δ_coarse
        = Real.rpow Δ_coarse (-s + ε_N) * Real.rpow Δ_coarse 1 := by rw [h_rpow1]
      _ = Real.rpow Δ_coarse ((-s + ε_N) + 1) := h_add.symm
      _ = Real.rpow Δ_coarse (-s + ε_N + 1) := by ring
    exact h4
  have h_exp_nonneg : 0 ≤ -s + ε_N + 1 := by linarith
  have h_leK : Real.rpow K (-C'_coarse) ≤ 1 := by
    have h9 : -C'_coarse ≤ 0 := by linarith
    have h10 : Real.rpow K (-C'_coarse) ≤ Real.rpow K 0 :=
      Real.rpow_le_rpow_of_exponent_le hK_ge1 h9
    simpa using h10
  have h_leδ : Real.rpow δ (C'_coarse * lam) ≤ 1 :=
    Real.rpow_le_one hδ_pos.le hδ_lt_one.le (by positivity)
  have h_leΔ : Real.rpow Δ_coarse (-s + ε_N + 1) ≤ 1 :=
    Real.rpow_le_one hΔ_pos.le hΔ_lt_one.le h_exp_nonneg
  have h_nonnegK : 0 ≤ Real.rpow K (-C'_coarse) := Real.rpow_nonneg (by linarith) _
  have h_nonnegδ : 0 ≤ Real.rpow δ (C'_coarse * lam) := Real.rpow_nonneg hδ_pos.le _
  have h_nonnegΔ : 0 ≤ Real.rpow Δ_coarse (-s + ε_N + 1) := Real.rpow_nonneg hΔ_pos.le _
  have h_prod1 : Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) ≤ 1 := by
    calc
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)
        ≤ 1 * Real.rpow δ (C'_coarse * lam) := by exact mul_le_mul_of_nonneg_right h_leK h_nonnegδ
      _ ≤ 1 * 1 := by exact mul_le_mul_of_nonneg_left h_leδ (by norm_num)
      _ = 1 := by norm_num
  have h_prod : (Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) *
      Real.rpow Δ_coarse (-s + ε_N + 1) ≤ 1 := by
    calc
      (Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) * Real.rpow Δ_coarse (-s + ε_N + 1)
        ≤ 1 * Real.rpow Δ_coarse (-s + ε_N + 1) := by exact mul_le_mul_of_nonneg_right h_prod1 h_nonnegΔ
      _ ≤ 1 * 1 := by exact mul_le_mul_of_nonneg_left h_leΔ (by norm_num)
      _ = 1 := by norm_num
  have h_product_le : (Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) *
      Real.rpow Δ_coarse (-s + ε_N + 1) ≤ 1 := h_prod
  have h_main : MΔ * ((Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) *
      Real.rpow Δ_coarse (-s + ε_N + 1)) ≤ MΔ := by
    have hM_nonneg : 0 ≤ MΔ := hMΔ_nonneg
    calc MΔ * ((Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) * Real.rpow Δ_coarse (-s + ε_N + 1))
      ≤ MΔ * 1 := mul_le_mul_of_nonneg_left h_product_le hM_nonneg
    _ = MΔ := by ring
  have h_rhs_eq : Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * MΔ *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ =
      MΔ * ((Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) *
        Real.rpow Δ_coarse (-s + ε_N + 1)) := by
    have h_step1 : Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * MΔ *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        (Real.rpow Δ_coarse (-s + ε_N) * PΔ) =
        1 * MΔ * Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
          (Real.rpow Δ_coarse (-s + ε_N) * PΔ) := by
      rw [h1] <;> ring
    have h_step2 : 1 * MΔ * Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        (Real.rpow Δ_coarse (-s + ε_N) * PΔ) =
        MΔ * ((Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) *
          Real.rpow Δ_coarse (-s + ε_N + 1)) := by
      rw [h2] <;> ring
    have h_assoc : Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * MΔ *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ =
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * MΔ *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        (Real.rpow Δ_coarse (-s + ε_N) * PΔ) := by ring
    rw [h_assoc, h_step1, h_step2]
  rw [h_rhs_eq]
  exact le_trans h_main hTΔ_ge

/-- m=1 smallness bound: Poly factors absorbed, product ≤ 1. -/
lemma assembly_m1_smallness
    {s ε_N η : ℝ} {MΔ : ℕ} {K : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hεN : 0 < ε_N) (hη : 0 < η)
    (hK_ge1 : 1 ≤ K)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (lam : ℝ) (hlam : 0 < lam)
    (TΔ_card : ℝ) (hTΔ_ge : TΔ_card ≥ (MΔ : ℝ))
    (k : ℕ) (hδ_eq : δ = dyadicDelta k)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow δ (-lam))
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    (PΔ : ℝ) (hPΔ_pos : 0 < PΔ) (hPΔ_le : PΔ ≤ Real.rpow 2 η) :
    TΔ_card ≥
      (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ := by
  have hK_pos : 0 < K := by linarith
  set Poly : ℝ := (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 with hPoly_def
  have hPoly_pos : 0 < Poly := by positivity
  have hδlam_le : Real.rpow δ lam ≤ Poly⁻¹ := by
    have h1 : Real.rpow δ (-lam) = (Real.rpow δ lam)⁻¹ := by
      simpa using Real.rpow_neg hδ_pos.le lam
    rw [h1] at h_poly_K_le_δlam
    have h_pos2 : 0 < Real.rpow δ lam := Real.rpow_pos_of_pos hδ_pos _
    have h : Poly * Real.rpow δ lam ≤ 1 := by
      calc Poly * Real.rpow δ lam
        ≤ (Real.rpow δ lam)⁻¹ * Real.rpow δ lam := by gcongr
      _ = 1 := by field_simp [h_pos2.ne'] <;> ring
    have h3 : Real.rpow δ lam ≤ Poly⁻¹ := by
      calc Real.rpow δ lam
        = (Poly * Real.rpow δ lam) / Poly := by field_simp [hPoly_pos.ne'] <;> ring
      _ ≤ 1 / Poly := by gcongr
      _ = Poly⁻¹ := by simp
    exact h3
  have h3 : Poly⁻¹ ≤ (Real.rpow 2 (s + η - ε_N))⁻¹ := by
    have h_pos_rpow : 0 < Real.rpow 2 (s + η - ε_N) := Real.rpow_pos_of_pos (by norm_num) _
    have h_le : Real.rpow 2 (s + η - ε_N) ≤ Poly := h_k_large
    have h_result : (1 : ℝ) / Poly ≤ (1 : ℝ) / Real.rpow 2 (s + η - ε_N) :=
      one_div_le_one_div_of_le h_pos_rpow h_le
    have h_conv1 : Poly⁻¹ = (1 : ℝ) / Poly := by simp
    have h_conv2 : (Real.rpow 2 (s + η - ε_N))⁻¹ = (1 : ℝ) / Real.rpow 2 (s + η - ε_N) := by simp
    rw [h_conv1, h_conv2]; exact h_result
  have h4 : (Real.rpow 2 (s + η - ε_N))⁻¹ = Real.rpow 2 (ε_N - s - η) := by
    have h5 : ε_N - s - η = -(s + η - ε_N) := by ring
    rw [h5]
    have h6 : Real.rpow 2 (-(s + η - ε_N)) = (Real.rpow 2 (s + η - ε_N))⁻¹ := by
      exact Real.rpow_neg (by norm_num) (s + η - ε_N)
    exact h6.symm
  have hδlam_le2 : Real.rpow δ lam ≤ Real.rpow 2 (ε_N - s - η) :=
    le_trans hδlam_le (le_trans h3 (le_of_eq h4))
  have h_half_exp : Real.rpow (1 / 2 : ℝ) (-s + ε_N) = Real.rpow 2 (s - ε_N) := by
    have h_pos2 : (0 : ℝ) < (2 : ℝ) := by norm_num
    have h_base : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [h_base]
    have h6 : Real.rpow ((2 : ℝ)⁻¹) (-s + ε_N) = Real.rpow (2 : ℝ) (-(-s + ε_N)) := by
      have h_def1 : Real.rpow ((2 : ℝ)⁻¹) (-s + ε_N) =
          Real.exp (Real.log ((2 : ℝ)⁻¹) * (-s + ε_N)) :=
        Real.rpow_def_of_pos (by positivity) (-s + ε_N)
      have h_def2 : Real.rpow (2 : ℝ) (-(-s + ε_N)) =
          Real.exp (Real.log (2 : ℝ) * (-(-s + ε_N))) :=
        Real.rpow_def_of_pos h_pos2 (-(-s + ε_N))
      rw [h_def1, h_def2]
      have h_log : Real.log ((2 : ℝ)⁻¹) = -Real.log (2 : ℝ) := by simp
      rw [h_log] <;> ring_nf
    rw [h6]
    have h7 : -(-s + ε_N) = s - ε_N := by ring
    rw [h7]
  have h_product_le_one : Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ ≤ 1 := by
    rw [h_half_exp]
    have hK_inv : Real.rpow K (-1) = K⁻¹ := by simpa using Real.rpow_neg_one K
    rw [hK_inv]
    have h_posδ : 0 ≤ Real.rpow δ lam := Real.rpow_nonneg hδ_pos.le _
    have h_pos2 : 0 ≤ Real.rpow 2 (s - ε_N) := Real.rpow_nonneg (by norm_num) _
    have h_posP : 0 ≤ PΔ := hPΔ_pos.le
    have h_rpow_sum : Real.rpow 2 (ε_N - s - η) * Real.rpow 2 (s - ε_N) = Real.rpow 2 (-η) := by
      have h_add : Real.rpow (2 : ℝ) (ε_N - s - η) * Real.rpow (2 : ℝ) (s - ε_N) =
          Real.rpow (2 : ℝ) ((ε_N - s - η) + (s - ε_N)) :=
        (Real.rpow_add (by norm_num) (ε_N - s - η) (s - ε_N)).symm
      have h_sum : (ε_N - s - η) + (s - ε_N) = -η := by ring
      rw [h_add, h_sum]
    have h_rpow_cancel : Real.rpow 2 (-η) * Real.rpow 2 η = 1 := by
      have h_add : Real.rpow (2 : ℝ) (-η) * Real.rpow (2 : ℝ) η =
          Real.rpow (2 : ℝ) ((-η) + η) :=
        (Real.rpow_add (by norm_num) (-η) η).symm
      have h_sum : (-η) + η = 0 := by ring
      rw [h_add, h_sum]; simp
    calc
      K⁻¹ * Real.rpow δ lam * Real.rpow 2 (s - ε_N) * PΔ
        ≤ K⁻¹ * Real.rpow 2 (ε_N - s - η) * Real.rpow 2 (s - ε_N) * PΔ := by gcongr <;> linarith
      _ = K⁻¹ * (Real.rpow 2 (ε_N - s - η) * Real.rpow 2 (s - ε_N)) * PΔ := by ring
      _ = K⁻¹ * Real.rpow 2 (-η) * PΔ := by rw [h_rpow_sum] <;> ring
      _ ≤ K⁻¹ * Real.rpow 2 (-η) * Real.rpow 2 η := by
          have h_nonneg : 0 ≤ K⁻¹ * Real.rpow 2 (-η) := by
            have h1 : 0 < K⁻¹ := by positivity
            have h2 : 0 < Real.rpow 2 (-η) := Real.rpow_pos_of_pos (by norm_num) _
            exact mul_pos h1 h2 |>.le
          exact mul_le_mul_of_nonneg_left hPΔ_le h_nonneg
      _ = K⁻¹ * (Real.rpow 2 (-η) * Real.rpow 2 η) := by ring
      _ = K⁻¹ * 1 := by rw [h_rpow_cancel]
      _ = K⁻¹ := by ring
      _ ≤ 1 := by
        have h : K⁻¹ ≤ 1 := by
          calc K⁻¹ = 1 / K := by simp
            _ ≤ 1 / 1 := by gcongr
            _ = 1 := by norm_num
        exact h
  have h_goal : (MΔ : ℝ) * (Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ) ≤ (MΔ : ℝ) := by
    have hM_nonneg : 0 ≤ (MΔ : ℝ) := by positivity
    calc
      (MΔ : ℝ) * (Real.rpow K (-1) * Real.rpow δ lam *
          Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ)
        ≤ (MΔ : ℝ) * 1 := mul_le_mul_of_nonneg_left h_product_le_one hM_nonneg
      _ = (MΔ : ℝ) := by ring
  have h_final : (MΔ : ℝ) ≥
      (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ := by
    have h_assoc : (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
        Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ =
        (MΔ : ℝ) * (Real.rpow K (-1) * Real.rpow δ lam *
        Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ) := by ring
    rw [h_assoc]; exact h_goal
  exact le_trans h_final hTΔ_ge

/-- m=1 normal/good coarse bound. -/
lemma assembly_coarse_bound_m1_normal_good
    {s ε_N η : ℝ} {MΔ : ℕ} {K : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hεN : 0 < ε_N) (hη : 0 < η)
    (hK_ge1 : 1 ≤ K)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (lam : ℝ) (hlam : 0 < lam)
    (TΔ_card : ℝ) (hTΔ_ge : TΔ_card ≥ (MΔ : ℝ))
    (k : ℕ) (hδ_eq : δ = dyadicDelta k)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow δ (-lam))
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    (PΔ : ℝ) (hPΔ_pos : 0 < PΔ) (hPΔ_le : PΔ ≤ Real.rpow 2 η)
    (C_coarse : ℝ) (hC0 : C_coarse = 0)
    (C'_coarse : ℝ) (hC'1 : C'_coarse = 1)
    (Δ_coarse : ℝ) (hΔ_eq : Δ_coarse = dyadicDelta 1) :
    TΔ_card ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
  have hΔ_half : Δ_coarse = (1 / 2 : ℝ) := by
    rw [hΔ_eq]; simp [dyadicDelta] <;> norm_num
  have h1 : Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) = 1 := by
    have hC0' : -C_coarse = 0 := by linarith [hC0]
    rw [hC0']; simp
  have h_main : TΔ_card ≥
      (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ :=
    assembly_m1_smallness hs hs1 hεN hη hK_ge1 δ hδ_pos hδ_lt_one lam hlam
      TΔ_card hTΔ_ge k hδ_eq h_poly_K_le_δlam h_k_large PΔ hPΔ_pos hPΔ_le
  rw [h1, hC'1, hΔ_half]
  have h2 : Real.rpow δ (1 * lam) = Real.rpow δ lam := by ring_nf
  rw [h2]
  have h3 : (1 : ℝ) * (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ =
      (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ := by ring
  rw [h3]
  exact h_main

/-- Standalone coarse bound dispatch for the first scale. -/
lemma coarse_bound_assembly
    {n m k M MΔ : ℕ}
    {s t τ ε_G η ε_N ε_inc C_P lam : ℝ}
    {K CΔ C_coarse C'_coarse K_p5 : ℝ}
    {PΔ : ℝ}
    {config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {Δ : Fin (n + 1) → ℝ}
    {scaleClass : Fin n → ScaleClass}
    {C_between : Fin n → ℝ}
    {N : Fin n → ℕ}
    {P : Finset (DyadicSquare k)}
    (hnm : m ≤ k)
    (j0 : Fin n)
    (hj0 : j0.val = 0)
    -- Core configurations
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    -- B1 bridge outputs
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty' : P.Nonempty)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_card_bound : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K * coarseConfig.P₀.card)
    (hCΔ_bounds1 : CΔ ≤ K * Real.rpow (dyadicDelta k) (-lam))
    (hCΔ_bounds2 : Real.rpow (dyadicDelta k) (-lam) ≤ K * CΔ)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Scale data
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (Δ_coarse : ℝ)
    (hΔ_coarse_def : Δ_coarse = Δ 1)
    (hΔ_coarse_pos : 0 < Δ_coarse)
    (hΔ_lt_one : Δ_coarse < 1)
    (δ : ℝ)
    (hδ_def : δ = dyadicDelta k)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    -- Constants and bounds
    (hK_ge1 : 1 ≤ K)
    (hK_pos : 0 < K)
    (hK_bound : K ≤ (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam))
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    (hK_p5_pos : 0 < K_p5)
    (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_spec : ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (m : ℕ), 2 ≤ m →
      ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M →
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
    (hCP : 1 ≤ C_P)
    -- Parameter positivity
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t)
    (hεG : 0 < ε_G) (hη : 0 < η) (hεN : 0 < ε_N)
    (hτ_pos : 0 < τ) (hlam : 0 < lam)
    -- Absorption hypotheses
    (h_absorb_coarse : scaleClass ⟨0, by omega⟩ = ScaleClass.normal →
        Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) ε_N)
    (h_absorb_coarse_good : ∀ (t_j : ℝ), scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j →
        Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2)) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) (2 * ε_G + ε_N))
    -- Improved incidence for good case
    (h_good_improved_incidence : ∀ (t_j : ℝ),
        scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j →
        ∀ (hnm' : m ≤ k) (K' CΔ' : ℝ) (MΔ' : ℕ)
          (coarseConfig' : CTNiceConfiguration m s CΔ' MΔ')
          (P' : Finset (DyadicSquare k))
          (hP_sub' : P' ⊆ config.P₀)
          (hcoarse_P_eq' : coarseConfig'.P₀ = P'.image (InductionConfigurations.containingSquare hnm'))
          (h_card_bound' : (config.P₀.image (InductionConfigurations.containingSquare hnm')).card ≤ K' * coarseConfig'.P₀.card)
          (hK_bound' : K' ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
          (hCΔ_bounds1' : CΔ' ≤ K' * Real.rpow (dyadicDelta k) (-lam))
          (hCΔ_bounds2' : Real.rpow (dyadicDelta k) (-lam) ≤ K' * CΔ')
          (h_slope_coarse' : ∀ T ∈ coarseConfig'.T₀, |T.slope| ≤ 1)
          (hP_nonempty' : P'.Nonempty),
        (coarseConfig'.T₀.card : ENNReal) ≥
          ENNReal.ofReal (Real.rpow (dyadicDelta m) (-(2 * s + ε_inc))))
    -- Extra hypotheses
    (h_tj_ge_t : ∀ (j : Fin n) (t_j : ℝ), scaleClass j = ScaleClass.good t_j → t ≤ t_j)
    (hε_inc_pos : 0 < ε_inc)
    (h_exp_condition : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    (hcoarse_P_nonempty : coarseConfig.P₀.Nonempty)
    (hMΔ_pos : 0 < MΔ)
    -- C_coarse definition
    (hC_coarse_def : C_coarse = if m = 1 then 0 else K_p5 + C_P + 8)
    (hC'_coarse_eq1 : C'_coarse = 1)
    (hPΔ_def : PΔ =
      ((∏ j ∈ ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood),
          Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) *
       (∏ j ∈ ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad),
          Δ (Fin.succ j) / Δ j.castSucc))) :
    (coarseConfig.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
      Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
  classical
  have hn_pos : 0 < n := by
    exact Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 j0)
  have j0_eq : j0 = (⟨0, hn_pos⟩ : Fin n) := by
    apply Fin.ext
    simpa using hj0
  let G0 : Finset (Fin n) := ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isGood)
  let B0 : Finset (Fin n) := ({j0} : Finset (Fin n)).filter (fun j => (scaleClass j).isBad)
  have hC'_coarse_ge1 : 1 ≤ C'_coarse := by
    rw [hC'_coarse_eq1] <;> norm_num
  have hC'1 : C'_coarse = 1 := hC'_coarse_eq1
  have hPΔ_pos : 0 < PΔ := by
    rw [hPΔ_def]
    apply mul_pos <;> apply Finset.prod_pos <;> intro j _
    · have h1 : 0 < Δ j.castSucc := hcfg.hΔ_pos j.castSucc
      have h2 : 0 < Δ (Fin.succ j) := hcfg.hΔ_pos (Fin.succ j)
      exact Real.rpow_pos_of_pos (div_pos h1 h2) _
    · have h1 : 0 < Δ (Fin.succ j) := hcfg.hΔ_pos (Fin.succ j)
      have h2 : 0 < Δ j.castSucc := hcfg.hΔ_pos j.castSucc
      exact div_pos h1 h2
  have hTΔ_ge : (coarseConfig.T₀.card : ℝ) ≥ (MΔ : ℝ) := by
    rcases hcoarse_P_nonempty with ⟨p, hp⟩
    have h1 : coarseConfig.tubeFamily p hp ⊆ coarseConfig.T₀ := coarseConfig.h_subset p hp
    have h2 : (coarseConfig.tubeFamily p hp).card = MΔ := coarseConfig.h_size p hp
    have h3 : (coarseConfig.tubeFamily p hp).card ≤ coarseConfig.T₀.card := Finset.card_le_card h1
    rw [h2] at h3
    exact_mod_cast h3
  let scaleClass0 := scaleClass j0
  have h1lt : 1 < n + 1 := by linarith
  have h_j1 : (Fin.succ j0 : Fin (n + 1)) = 1 := by
    apply Fin.ext
    simp [j0_eq, Fin.ext_iff, Nat.mod_eq_of_lt h1lt]
    <;> omega
  have h_j0 : (j0.castSucc : Fin (n + 1)) = 0 := by
    apply Fin.ext
    simpa using hj0
  by_cases h_bad : scaleClass0 = ScaleClass.bad
  · -- Bad first scale
    have hbad2 : scaleClass j0 = ScaleClass.bad := by simpa [scaleClass0] using h_bad
    have h_good_false : (scaleClass j0).isGood = false := by rw [hbad2] <;> rfl
    have h_bad_true : (scaleClass j0).isBad = true := by rw [hbad2] <;> rfl
    have hPΔ : PΔ = Δ_coarse := by
      have h : PΔ = Δ (Fin.succ j0) / Δ j0.castSucc := by
        rw [hPΔ_def]
        simp [h_good_false, h_bad_true, Finset.filter_singleton, Finset.prod_singleton]
        <;> rfl
      rw [h, h_j1, h_j0, hΔ_coarse_def, hcfg.hΔ_start] <;> ring
    by_cases h_m1 : m = 1
    · -- m=1 bad
      have hC0 : C_coarse = 0 := by
        rw [hC_coarse_def, if_pos h_m1]
      have hMΔ_nonneg : 0 ≤ (MΔ : ℝ) := by positivity
      exact assembly_coarse_bound_m1_bad s ε_N lam
        hΔ_coarse_pos hΔ_lt_one hδ_pos hδ_lt_one hK_ge1 hC'_coarse_ge1 hlam
        hs hs1 hεN hC0 hPΔ hTΔ_ge hMΔ_nonneg
    · -- m≥2 bad
      have h_m_ne0 : m ≠ 0 := by
        intro h
        have h3 : Δ_coarse = 1 := by
          rw [hΔ_coarse_def, hm_eq2, h] <;> dsimp only [dyadicDelta] <;> norm_num
        rw [h3] at hΔ_lt_one
        <;> linarith
      have h_m2 : m ≥ 2 := by omega
      have hC_coarse_pos : 0 < C_coarse := by
        rw [hC_coarse_def, if_neg h_m1] <;> linarith [hK_p5_ge1, hCP]
      have hL_ge1 : 1 ≤ Real.log (1 / Δ_coarse) := by
        have h2 : Δ_coarse = dyadicDelta m := by
          rw [hΔ_coarse_def, hm_eq2]
        rw [h2]
        exact assembly_dyadicDelta_log_ge_one h_m2
      have hC'_coarse_pos : 0 < C'_coarse := by
        rw [hC'_coarse_eq1] <;> norm_num
      exact coarse_bound_bad hs hs1 hεN hC_coarse_pos hC'_coarse_pos hK_ge1
        δ Δ_coarse hδ_pos hΔ_coarse_pos hΔ_lt_one hL_ge1 hδ_lt_one lam hlam
        (coarseConfig.T₀.card : ℝ) hTΔ_ge PΔ hPΔ
  · -- Normal/good first scale
    by_cases h_m1 : m = 1
    · -- m=1 normal/good
      have hC0 : C_coarse = 0 := by
        rw [hC_coarse_def, if_pos h_m1]
      have hΔ1_eq : Δ 1 = dyadicDelta 1 := by
        rw [hm_eq2, h_m1]
      have hΔ_eq : Δ_coarse = dyadicDelta 1 := by
        rw [hΔ_coarse_def, hΔ1_eq]
      have hδ_eq' : δ = dyadicDelta k := hδ_def
      have hPΔ_le : PΔ ≤ Real.rpow 2 η := by
        have h_sc : scaleClass j0 ≠ ScaleClass.bad := by
          intro h; exact h_bad h
        cases h_sc2 : scaleClass j0 with
        | normal =>
          have h_good_false : (scaleClass j0).isGood = false := by rw [h_sc2] <;> rfl
          have h_bad_false : (scaleClass j0).isBad = false := by rw [h_sc2] <;> rfl
          have hP : PΔ = 1 := by
            rw [hPΔ_def]
            simp [h_good_false, h_bad_false, Finset.filter_singleton] <;> norm_num
          rw [hP]
          have h3 : 0 ≤ η := by linarith
          have h4 : (1 : ℝ) ≤ Real.rpow 2 η := by
            have h5 : Real.rpow 2 η ≥ Real.rpow 2 0 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
            simpa using h5
          exact h4
        | good t_j =>
          have h_good_true : (scaleClass j0).isGood = true := by rw [h_sc2] <;> rfl
          have h_bad_false : (scaleClass j0).isBad = false := by rw [h_sc2] <;> rfl
          have hP : PΔ = Real.rpow (Δ 0 / Δ 1) η := by
            rw [hPΔ_def]
            simp [h_good_true, h_bad_false, Finset.filter_singleton, Finset.prod_singleton, Finset.prod_empty, mul_one]
            <;> congr <;> simp [h_j0, h_j1]
          rw [hP]
          have hΔ0_eq1 : Δ 0 = 1 := hcfg.hΔ_start
          have h_ratio : Δ 0 / Δ 1 = 2 := by
            rw [hΔ0_eq1, hΔ1_eq]
            simp [dyadicDelta] <;> norm_num
          rw [h_ratio] <;> linarith
        | bad => contradiction
      have h_poly_K_le_δlam' : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow δ (-lam) := by
        rw [hδ_eq']
        exact h_poly_K_le_δlam
      exact assembly_coarse_bound_m1_normal_good hs hs1 hεN hη hK_ge1
        δ hδ_pos hδ_lt_one lam hlam
        (coarseConfig.T₀.card : ℝ) hTΔ_ge k hδ_eq'
        h_poly_K_le_δlam' h_k_large PΔ hPΔ_pos hPΔ_le
        C_coarse hC0 C'_coarse hC'1 Δ_coarse hΔ_eq
    · -- m≥2 normal/good
      have h_m_ne0 : m ≠ 0 := by
        intro h
        have h3 : Δ_coarse = 1 := by
          rw [hΔ_coarse_def, hm_eq2, h] <;> dsimp only [dyadicDelta] <;> norm_num
        rw [h3] at hΔ_lt_one <;> linarith
      have h_m2 : m ≥ 2 := by omega
      have hj0_eq : j0 = ⟨0, by omega⟩ := Fin.ext hj0
      have hΔ0' : Δ 0 = 1 := hcfg.hΔ_start
      have hΔ1' : Δ 1 = Δ_coarse := by simp [hΔ_coarse_def]
      have hΔ_coarse_eq' : Δ_coarse = dyadicDelta m :=
        hΔ_coarse_def.trans hm_eq2
      have hC_coarse_val' : C_coarse = K_p5 + C_P + 8 := by
        rw [hC_coarse_def, if_neg h_m1]
      have hLbar_ge1' : 1 ≤ Real.log (1 / Δ_coarse) := by
        rw [hΔ_coarse_eq']
        exact assembly_dyadicDelta_log_ge_one h_m2
      have hδ_le_delta' : δ ≤ Δ_coarse := by
        rw [hδ_def, hΔ_coarse_eq']
        have h4 : m ≤ k := hnm
        have h5 : (2 : ℝ)^m ≤ (2 : ℝ)^k := pow_le_pow_right₀ (by norm_num) h4
        have h6 : 0 < (2 : ℝ)^m := by positivity
        exact one_div_le_one_div_of_le h6 h5
      have hMΔ_pos' : 0 < MΔ := hMΔ_pos
      by_cases h_normal_case : scaleClass0 = ScaleClass.normal
      · -- m≥2 normal
        have h_normal' : scaleClass j0 = ScaleClass.normal := by simpa [scaleClass0] using h_normal_case
        have h_good_false : (scaleClass j0).isGood = false := by rw [h_normal'] <;> rfl
        have h_bad_false : (scaleClass j0).isBad = false := by rw [h_normal'] <;> rfl
        have hPΔ_eq1 : PΔ = 1 := by
          rw [hPΔ_def]
          simp [h_good_false, h_bad_false, Finset.filter_singleton] <;> norm_num
        have h_main_no_PΔ := normal_coarse_bound
          (N := N)
          (hcfg := hcfg) (hB1 := hB1)
          (P := P) (hP_sub := hP_sub) (hP_nonempty' := hP_nonempty')
          (hnm := hnm) (hcoarse_P_eq := hcoarse_P_eq) (h_card_bound := h_card_bound)
          (hj0 := by simpa using hj0)
          (h_normal := h_normal')
          (hΔ0 := hΔ0') (hΔ1 := hΔ1') (hΔ_coarse_eq := hΔ_coarse_eq')
          (hs := hs) (hs1 := hs1) (hst := hst)
          (hεG := hεG) (hη := hη) (hεN := hεN)
          (hτ_pos := hτ_pos) (hCP := hCP) (hlam := hlam)
          (hK_ge1 := hK_ge1) (hK_pos := hK_pos)
          (hK_bound := hK_bound)
          (h_poly_K_le_δlam := h_poly_K_le_δlam)
          (hCΔ_bounds1 := hCΔ_bounds1) (hCΔ_bounds2 := hCΔ_bounds2)
          (hC_coarse_val := hC_coarse_val')
          (hC'_coarse_ge1 := hC'_coarse_ge1)
          (hK_p5_pos := hK_p5_pos) (hK_p5_ge1 := hK_p5_ge1)
          (hK_p5_spec_orig := hK_p5_spec)
          (hm_ge2 := h_m2)
          (hΔ_coarse_pos := hΔ_coarse_pos) (hΔ_coarse_lt_one := hΔ_lt_one)
          (hδ_eq := hδ_def)
          (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
          (hδ_le_delta := hδ_le_delta')
          (hLbar_ge1 := hLbar_ge1')
          (hMΔ_pos := hMΔ_pos')
          (h_slope_coarse := h_slope_coarse)
          (h_absorb_coarse := by
            have h_normal'' : scaleClass ⟨0, by omega⟩ = ScaleClass.normal := by
              rw [←j0_eq]; exact h_normal'
            exact h_absorb_coarse h_normal'')
        rw [hPΔ_eq1]
        simpa using h_main_no_PΔ
      · -- m≥2 good
        have h_not_bad : scaleClass0 ≠ ScaleClass.bad := by
          simpa [scaleClass0] using h_bad
        have h_not_normal : scaleClass0 ≠ ScaleClass.normal := by tauto
        cases h_sc2 : scaleClass0 with
        | normal => exact False.elim (h_not_normal h_sc2)
        | bad => exact False.elim (h_not_bad h_sc2)
        | good t_j =>
          have h_good' : scaleClass j0 = ScaleClass.good t_j := by simpa [scaleClass0] using h_sc2
          have h_good_true : (scaleClass j0).isGood = true := by rw [h_good'] <;> rfl
          have h_bad_false : (scaleClass j0).isBad = false := by rw [h_good'] <;> rfl
          have hPΔ_good : PΔ = Real.rpow (1 / Δ_coarse) η := by
            rw [hPΔ_def]
            simp [h_good_true, h_bad_false, Finset.filter_singleton, Finset.prod_singleton, Finset.prod_empty, mul_one]
            rw [h_j0, h_j1, hΔ0', hΔ1']
            have h_inv : (1 / Δ_coarse) = Δ_coarse⁻¹ := by field_simp [hΔ_coarse_pos.ne']
            rw [h_inv]
          have h_incidence : (coarseConfig.T₀.card : ENNReal) ≥
              ENNReal.ofReal (Real.rpow Δ_coarse (-(2 * s + ε_inc))) := by
            have h_good'' : scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j := by
              rw [←j0_eq]; exact h_good'
            have h_raw := h_good_improved_incidence t_j h_good'' hnm K CΔ MΔ
              coarseConfig P hP_sub hcoarse_P_eq h_card_bound
              hK_bound hCΔ_bounds1 hCΔ_bounds2 h_slope_coarse
              hP_nonempty'
            simpa [hΔ_coarse_eq'] using h_raw
          have h_main_no_PΔ := good_coarse_bound
            (t_j := t_j)
            (N := N)
            (hcfg := hcfg) (hB1 := hB1)
            (P := P) (hP_sub := hP_sub) (hP_nonempty' := hP_nonempty')
            (hnm := hnm) (hcoarse_P_eq := hcoarse_P_eq) (h_card_bound := h_card_bound)
            (hj0 := by simpa using hj0)
            (h_good := h_good')
            (h_tj_ge_t := h_tj_ge_t)
            (hΔ0 := hΔ0') (hΔ1 := hΔ1') (hΔ_coarse_eq := hΔ_coarse_eq')
            (hs := hs) (hs1 := hs1) (hst := hst)
            (hεG := hεG) (hη := hη) (hεN := hεN)
            (hε_inc := hε_inc_pos)
            (hτ_pos := hτ_pos) (hCP := hCP) (hlam := hlam)
            (hK_ge1 := hK_ge1) (hK_pos := hK_pos)
            (hK_bound := hK_bound)
            (h_poly_K_le_δlam := h_poly_K_le_δlam)
            (hCΔ_bounds1 := hCΔ_bounds1) (hCΔ_bounds2 := hCΔ_bounds2)
            (hC_coarse_val := hC_coarse_val')
            (hC'_coarse_ge1 := hC'_coarse_ge1)
            (hK_p5_pos := hK_p5_pos) (hK_p5_ge1 := hK_p5_ge1)
            (hK_p5_spec_orig := hK_p5_spec)
            (hm_ge2 := h_m2)
            (hΔ_coarse_pos := hΔ_coarse_pos) (hΔ_coarse_lt_one := hΔ_lt_one)
            (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
            (hδ_eq_dyadic := hδ_def)
            (hδ_le_delta := hδ_le_delta')
            (hLbar_ge1 := hLbar_ge1')
            (hMΔ_pos := hMΔ_pos')
            (h_slope_coarse := h_slope_coarse)
            (h_exp_condition_v2 := h_exp_condition)
            (h_improved_incidence_coarse := h_incidence)
            (h_absorb_good := by
              have h_good'' : scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j := by
                rw [←j0_eq]; exact h_good'
              exact h_absorb_coarse_good t_j h_good'')
            (PΔ := PΔ)
            (hPΔ_def := hPΔ_def)
          simpa using h_main_no_PΔ

end Prop73Restructure

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
