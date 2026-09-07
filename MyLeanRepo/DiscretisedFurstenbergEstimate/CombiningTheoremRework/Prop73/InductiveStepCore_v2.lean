module

/-
  Inductive Step Core v2 — Correct-contract version

  Core inductive step for the Prop73 combining induction (n ≥ 2).
  Decomposes the first coarse scale via the B1 bridge, applies the
  inductive hypothesis to the fine tail, and combines coarse and fine
  bounds to produce the final ENNReal lower bound.

  Key design:
  - Conditional C_coarse: 0 if m=1, else K_p5 + C_P + 8 (degree-7 B1 factor + margin)
  - Equation-(89) smallness hypothesis for fine C_between transfer
  - Main lemma inductive_step_core_v2 is COMPLETE — both all-tail-bad
    and non-all-bad branches are proved via inductive_step_core_v2_body.

  Helper lemmas (this file):
  - finset_product_split: generic product decomposition
  - coarse_bound_m1_bad_helper: m=1 bad first-scale bound
  - m1_coarse_bound_smallness / coarse_bound_m1_normal_good: m=1 normal/good bounds

  General arithmetic/log helpers (C', C_coarse, δ_k bounds, polynomial
  absorption, configuration weakening) live in InductiveStepCore_v2_Helpers.

  Whiteprint node: combining_theorem_genuine / inductive_step_core_v2
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2_Helpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.TailSplit
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigSublemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSourceData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseGeometricData
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseSsetConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BetweenScalesToSset
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundDispatcher
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigThinning
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NormalCoarseBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCoarseBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCaseImprovedIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseBoundAssembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.ProductSplittingExtra
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.NonAllBadArithmetic
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2_Body
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineBranchHcfgFine
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadAbsorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadBranch
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

/-- Generic helper: split a product over univ.filter p into a product over
{j0}.filter p times a product over (univ.erase j0).filter p. -/
lemma finset_product_split {n : ℕ} {j0 : Fin n} {α : Type*} [CommMonoid α]
    (p : Fin n → Prop) [DecidablePred p] (f : Fin n → α) :
    (∏ j ∈ ({j0} : Finset (Fin n)).filter p, f j) *
    (∏ j ∈ (Finset.univ.erase j0).filter p, f j) =
    ∏ j ∈ Finset.univ.filter p, f j := by
  have h_disj : Disjoint ({j0} : Finset (Fin n)) (Finset.univ.erase j0) := by
    simp [Finset.disjoint_left]
  have h_union : ({j0} : Finset (Fin n)) ∪ Finset.univ.erase j0 = Finset.univ := by
    ext x; simp [Finset.mem_erase] <;> tauto
  have h_filter_union : (({j0} : Finset (Fin n)) ∪ Finset.univ.erase j0).filter p =
      ({j0} : Finset (Fin n)).filter p ∪ (Finset.univ.erase j0).filter p := by
    rw [Finset.filter_union]
  have h_disj' : Disjoint (({j0} : Finset (Fin n)).filter p) ((Finset.univ.erase j0).filter p) :=
    Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) h_disj
  rw [← Finset.prod_union h_disj', ← h_filter_union, h_union]

/-- Helper: m=1 bad first-scale coarse bound.

When m=1, Δ_coarse=1/2 and C_coarse=0. The logarithmic factor disappears,
and all remaining non-MΔ factors (K^(-C'_coarse), δ^(C'_coarse*lam),
Δ_coarse^(-s+ε_N+1)) are ≤ 1, so |TΔ| ≥ MΔ suffices. -/
lemma coarse_bound_m1_bad_helper
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
  have h_main : MΔ * ((Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) *
      Real.rpow Δ_coarse (-s + ε_N + 1)) ≤ MΔ := by
    calc MΔ * ((Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam)) * Real.rpow Δ_coarse (-s + ε_N + 1))
      ≤ MΔ * 1 := by gcongr
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

/-- Coarse bound for m=1 normal/good scale using global δ-smallness.

When C_coarse=0, the log factor disappears. The remaining non-MΔ factors
are K^(-1) · δ^lam · (1/2)^(-s+ε_N) · PΔ, shown ≤ 1 using polynomial
decay of δ^lam and exponent cancellation. -/
lemma m1_coarse_bound_smallness
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

/-- Coarse bound for m=1 normal/good first scale.

Converts Δ_coarse = 1/2 (since m=1) and C_coarse=0, C'_coarse=1,
then delegates to m1_coarse_bound_smallness. -/
lemma coarse_bound_m1_normal_good
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
  have hC'_eq : C'_coarse = 1 := hC'1
  have h_main : TΔ_card ≥
      (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ :=
    m1_coarse_bound_smallness hs hs1 hεN hη hK_ge1 δ hδ_pos hδ_lt_one lam hlam
      TΔ_card hTΔ_ge k hδ_eq h_poly_K_le_δlam h_k_large PΔ hPΔ_pos hPΔ_le
  rw [h1, hC'_eq, hΔ_half]
  have h2 : Real.rpow δ (1 * lam) = Real.rpow δ lam := by ring_nf
  rw [h2]
  have h3 : (1 : ℝ) * (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ =
      (MΔ : ℝ) * Real.rpow K (-1) * Real.rpow δ lam *
      Real.rpow (1 / 2 : ℝ) (-s + ε_N) * PΔ := by ring
  rw [h3]
  exact h_main



lemma inductive_step_core_v2
    {s t τ ε_G η ε_N C_P C_P_fine : ℝ} {n k M : ℕ}
    {C_fine C'_fine C C' : ℝ}
    (m : ℕ)
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hεG : 0 < ε_G) (hη : 0 < η)
    (hεN : 0 < ε_N) (hεN_le : ε_N ≤ ε_G)
    (hCP : 1 ≤ C_P) (hCP_fine : 1 ≤ C_P_fine)
    (C_n : ℝ) (hCn_ge1 : 1 ≤ C_n)
    (hCP_fine_eq : C_P_fine = C_P + 2 * C_n)
    (h2 : 2 ≤ n)
    (hC_fine_pos : 0 < C_fine) (hC'_fine_pos : 0 < C'_fine)
    (K_p5 : ℝ) (hK_p5_ge1 : 1 ≤ K_p5)
    (hK_p5_pos : 0 < K_p5)
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
    (ε_inc : ℝ)
    (h_eq89 : Real.log (1 / dyadicDelta k) ≥ Real.rpow τ (-(C_P_fine : ℝ)))
    (lam : ℝ) (hlam : 0 < lam)
    -- Pre-applied IH at fixed lam_tail = 2λ/τ, at C_P_fine
    (lam_tail : ℝ) (hlam_tail_pos : 0 < lam_tail)
    (hτ_lam_tail : τ * lam_tail = 2 * lam)
    (δ_tail : ℝ) (hδ_tail_pos : 0 < δ_tail)
    (h_ih_bound : ∀ (k' : ℕ), dyadicDelta k' ≤ δ_tail →
      ∀ (M' : ℕ)
        (config' : CTNiceConfiguration k' s (Real.rpow (dyadicDelta k') (-lam_tail)) M')
        (Δ' : Fin ((n - 1) + 1) → ℝ)
        (scaleClass' : Fin (n - 1) → ScaleClass)
        (N' : Fin (n - 1) → ℕ)
        (C_between' : Fin (n - 1) → ℝ),
        CombiningConfig s t τ (n - 1) ε_G η lam_tail ε_N C_P_fine C_between' k' M' config' Δ' scaleClass' N' →
        B1BridgeHypotheses k' config' →
        CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P_fine ε_inc (n - 1) lam_tail k' M' config' Δ' scaleClass' →
        (config'.T₀.card : ENNReal) ≥
          ENNReal.ofReal (combiningLowerBound (dyadicDelta k') (M' : ℝ) C_fine C'_fine lam_tail s ε_N η (n - 1) Δ' scaleClass'))
    (hδτ_le_dtail : Real.rpow (dyadicDelta k) τ ≤ δ_tail)
    (h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam))
    -- h_k_large: must be derived by caller from δ-smallness + upper bound on η (Prop 7.3).
    -- For fixed s,ε_N and bounded η, Poly(k) grows polynomially while 2^(s+η-ε_N) is constant,
    -- so this holds for all sufficiently large k (i.e. sufficiently small δ).
    (h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N))
    {A : ℝ} (hA_pos : 0 < A) (hA_ge1 : 1 ≤ A)
    (hA_eq : A = 2700 * 3145728 * (8 / Real.log 2)^7)
    (hC_pos : 0 < C) (hC'_pos : 0 < C')
    (hC_ge : C ≥ (1 + (7 : ℝ)) * (1 + (1 : ℝ) + C'_fine) + K_p5 + C_P + 8 + C_fine)
    (hC'_ge : C' ≥ (1 : ℝ) + 2 * C'_fine / τ)
    (hk : dyadicDelta k ≤ Real.exp (-A))
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (Δ : Fin (n + 1) → ℝ)
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (scaleClass : Fin n → ScaleClass)
    (N : Fin n → ℕ)
    (C_between : Fin n → ℝ)
    -- Coarse absorption for m≥2 normal case (conditional on normal scale):
    -- log(1/Δ_m)^(C_P+8) ≥ K_p5 * C_P_coarse_upper * 13 * 2^s * Δ_m^ε_N
    -- Caller proves this using h_C_between_normal + scale ratio (m ≥ kτ).
    (h_absorb_coarse : scaleClass ⟨0, by omega⟩ = ScaleClass.normal →
        Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) ε_N)
    -- Good-case coarse absorption (conditional on good scale):
    -- With 2ε_G+ε_N exponent, C_between * Δ_m^(2ε_G+ε_N) decays exponentially.
    (h_absorb_coarse_good : ∀ (t_j : ℝ), scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j →
        Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
        K_p5 * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
          max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2)) * 13 * (2 : ℝ) ^ s *
        Real.rpow (dyadicDelta m) (2 * ε_G + ε_N))
    -- Fine absorption for normal tail scales (conditional):
    -- Amplified thinning C_between absorbed by log(1/δbar)^C_P_fine * ratio^ε_N
    (h_absorb_fine_normal : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin (n - 1)), scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.normal →
        9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) *
          (4 : ℝ) ^ (n - 1) ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε_N)
    -- Fine absorption for good tail scales (conditional):
    (h_absorb_fine_good : ∀ (K : ℝ), 1 ≤ K →
      K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
      ∀ (j : Fin (n - 1)) (t_j : ℝ), scaleClass ⟨j.val + 1, by omega⟩ = ScaleClass.good t_j →
        9 * (C_between ⟨j.val + 1, by omega⟩) * 2 * K *
          (24 * Real.log (1 / dyadicDelta (k - m)) / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) *
          (4 : ℝ) ^ (n - 1) ≤
        Real.log (1 / dyadicDelta (k - m)) ^ C_P_fine *
          (Δ ⟨j.val + 1, by omega⟩ / Δ ⟨j.val + 2, by omega⟩) ^ ε_G)
    -- Improved coarse incidence bound for good first scale (supplied by caller).
    -- Absorption conditions (C_weaken, δR, h_est_body) are baked into the
    -- implementation by the outer wrapper, which chooses δ₀ small enough.
    (h_good_improved_incidence : ∀ (t_j : ℝ),
        scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j →
        ∀ (hnm : m ≤ k) (K' CΔ' : ℝ) (MΔ' : ℕ)
          (coarseConfig' : CTNiceConfiguration m s CΔ' MΔ')
          (P' : Finset (DyadicSquare k))
          (hP_sub' : P' ⊆ config.P₀)
          (hcoarse_P_eq' : coarseConfig'.P₀ = P'.image (InductionConfigurations.containingSquare hnm))
          (h_card_bound' : (config.P₀.image (InductionConfigurations.containingSquare hnm)).card ≤ K' * coarseConfig'.P₀.card)
          (hK_bound' : K' ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7)
          (hCΔ_bounds1' : CΔ' ≤ K' * Real.rpow (dyadicDelta k) (-lam))
          (hCΔ_bounds2' : Real.rpow (dyadicDelta k) (-lam) ≤ K' * CΔ')
          (h_slope_coarse' : ∀ T ∈ coarseConfig'.T₀, |T.slope| ≤ 1)
          (hP_nonempty' : P'.Nonempty),
        (coarseConfig'.T₀.card : ENNReal) ≥
          ENNReal.ofReal (Real.rpow (dyadicDelta m) (-(2 * s + ε_inc))))
    (hcfg : CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N)
    (hB1 : B1BridgeHypotheses k config)
    (h_uniform : UniformIncidenceData s t ε_inc)
    (hextra : CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass) :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass) := by
  have h_exists : ∃ (n_fine : ℕ), n = n_fine + 1 := ⟨n - 1, by omega⟩
  rcases h_exists with ⟨n_fine, h_n_eq⟩
  exact inductive_step_core_v2_body
    (m := m) (hs := hs) (hst := hst) (hs1 := hs1)
    (hτ := hτ) (hτ1 := hτ1) (hεG := hεG) (hη := hη)
    (hεN := hεN) (hεN_le := hεN_le) (hCP := hCP) (hCP_fine := hCP_fine)
    (C_n := C_n) (hCn_ge1 := hCn_ge1) (hCP_fine_eq := hCP_fine_eq)
    (h2 := h2) (hC_fine_pos := hC_fine_pos) (hC'_fine_pos := hC'_fine_pos)
    (K_p5 := K_p5) (hK_p5_ge1 := hK_p5_ge1) (hK_p5_pos := hK_p5_pos)
    (hK_p5_spec := hK_p5_spec) (ε_inc := ε_inc) (h_eq89 := h_eq89)
    (lam := lam) (hlam := hlam) (lam_tail := lam_tail) (hlam_tail_pos := hlam_tail_pos)
    (hτ_lam_tail := hτ_lam_tail) (δ_tail := δ_tail) (hδ_tail_pos := hδ_tail_pos)
    (h_ih_bound := h_ih_bound) (hδτ_le_dtail := hδτ_le_dtail)
    (h_poly_K_le_δlam := h_poly_K_le_δlam) (h_k_large := h_k_large)
    (A := A) (hA_pos := hA_pos) (hA_ge1 := hA_ge1) (hA_eq := hA_eq)
    (hC_pos := hC_pos) (hC'_pos := hC'_pos) (hC_ge := hC_ge) (hC'_ge := hC'_ge)
    (hk := hk) (config := config) (Δ := Δ) (hm_eq2 := hm_eq2)
    (scaleClass := scaleClass) (N := N) (C_between := C_between)
    (h_absorb_coarse := h_absorb_coarse)
    (h_absorb_coarse_good := h_absorb_coarse_good)
    (h_absorb_fine_normal := h_absorb_fine_normal)
    (h_absorb_fine_good := h_absorb_fine_good)
    (h_good_improved_incidence := h_good_improved_incidence)
    (hcfg := hcfg) (hB1 := hB1) (h_uniform := h_uniform) (hextra := hextra)
    (n_fine := n_fine) (h_n_eq := h_n_eq)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
