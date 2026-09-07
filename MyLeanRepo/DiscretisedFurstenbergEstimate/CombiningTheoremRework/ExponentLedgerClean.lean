module

/-
  Exponent Ledger — Common Threshold and Loss Accounting

  Tracks all exponent losses and proves they close at a common δ0,
  yielding N₀ ≥ δ^{-(2s+η)}.

  CORRECTED DIRECTION (per orchestrator correction):
  - Restriction/retention WORSENS the S-set constant: δ^{-εInc} → δ^{-(εInc + loss)}
  - Regularity budget: η + regularity_degradation ≤ εA
  - εA is chosen UPSTREAM by appendix_a_main, NOT set to ε - degradation.
  - Coarse branch budget: η ≤ coarseGain - localLoss - multiplicityLoss - loss_K - transferLoss

  Global parameter order:
  1. Unpack appendix_a_main → εA, δA
  2. Choose εInc (η) << εA*α0
  3. Prove η + every retained-regularity loss ≤ εA
  4. Choose δR ≤ δA and every absorption/frontend threshold
  5. Prove RegularIncidenceBody for u,δ quantified afterward

  Loss items and suppliers:
  - εA: appendix_a_main (upstream)
  - coarseGain: aurora (coarse two-case ratio, depends on εA)
  - localLoss: lagoon (fine normalized ratio base)
  - fiber_L: ember (logarithmic point retention, added to localLoss)
  - b1_retention: juniper (global point retention, added to localLoss)
  - multiplicityLoss: M lower bound absorption
  - loss_K: B1 bridge K absorption
  - regularity_degradation: thinning S-set constant degradation
  - transfer_loss: indigo (final card/Ncover transfer)

  Whiteprint node: combining_theorem_rework / exponent_ledger
  Status: IMPLEMENTED (corrected)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAlgebra
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.PolylogAbsorption
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Section6
open DirecretisedFurstenbergEstimate.SourceFacingTheorem61

/-! ========================================================================
   Loss ledger
   ======================================================================== -/

/-- Complete exponent loss ledger for the coarse branch.

    εA is the Appendix A parameter (chosen upstream).
    coarseGain is the gain from the coarse alternative (function of εA).
    regularity_degradation tracks S-set constant worsening from retention.
    All other fields are coarse-branch exponent losses. -/
structure LossLedger (s : ℝ) where
  εA : ℝ
  coarseGain : ℝ
  localLoss : ℝ
  multiplicityLoss : ℝ
  loss_K : ℝ
  fiber_L : ℝ
  b1_retention : ℝ
  regularity_degradation : ℝ
  transfer_loss : ℝ
  hεA_pos : 0 < εA
  hcoarseGain_pos : 0 < coarseGain
  hlocalLoss_nonneg : 0 ≤ localLoss
  hmultiplicityLoss_nonneg : 0 ≤ multiplicityLoss
  hloss_K_nonneg : 0 ≤ loss_K
  hfiber_L_nonneg : 0 ≤ fiber_L
  hb1_retention_nonneg : 0 ≤ b1_retention
  hregularity_degradation_nonneg : 0 ≤ regularity_degradation
  htransfer_loss_nonneg : 0 ≤ transfer_loss

/-- Total coarse-branch losses (excluding regularity_degradation, which is
    handled by the separate regularity budget). -/
def LossLedger.coarseBranchTotalLoss {s : ℝ} (L : LossLedger s) : ℝ :=
  L.localLoss + L.fiber_L + L.b1_retention +
  L.multiplicityLoss + L.loss_K + L.transfer_loss

/-- Coarse branch net gain = coarseGain - coarseBranchTotalLoss. -/
def LossLedger.coarseBranchNetGain {s : ℝ} (L : LossLedger s) : ℝ :=
  L.coarseGain - L.coarseBranchTotalLoss

/-- Regularity budget: η + regularity_degradation ≤ εA.
    This ensures the degraded S-set constant still satisfies Appendix A. -/
def LossLedger.regularityBudget {s : ℝ} (L : LossLedger s) (η : ℝ) : Prop :=
  η + L.regularity_degradation ≤ L.εA

/-- Coarse branch budget: η ≤ coarseBranchNetGain. -/
def LossLedger.coarseBranchBudget {s : ℝ} (L : LossLedger s) (η : ℝ) : Prop :=
  η ≤ L.coarseBranchNetGain

/-- Both budgets close. -/
def LossLedger.budgetCloses {s : ℝ} (L : LossLedger s) (η : ℝ) : Prop :=
  L.regularityBudget η ∧ L.coarseBranchBudget η

/-! ========================================================================
   Polylog absorption wrappers
   ======================================================================== -/

/-- Absorb a polylog UPPER bound: C * log(1/δ)^D ≤ δ^{-loss}.

    From polylog_absorption_core: δ^loss * |log δ|^D ≤ 1/C
    ⇒ C * δ^loss * log^D ≤ 1
    ⇒ C * log^D ≤ δ^{-loss}.

    Requires loss > 0, D > 0. -/
lemma absorb_polylog_upper
    (C D loss : ℝ) (hC_pos : 0 < C) (hD_pos : 0 < D) (hloss_pos : 0 < loss) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      C * (Real.log (1 / δ)) ^ D ≤ δ ^ (-loss) := by
  rcases polylog_absorption_core loss D (1 / C) hloss_pos hD_pos (by positivity) with
    ⟨δ_core, hδ_core_pos, hcore⟩
  let δ₀ := min δ_core (1 / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
  have hδ_lt_core : δ < δ_core := by
    calc δ < δ₀ := hδ_lt
         _ ≤ δ_core := min_le_left _ _
  have hδ_lt_one : δ < 1 := by
    calc δ < δ₀ := hδ_lt
         _ ≤ 1 / 2 := min_le_right _ _
         _ < 1 := by norm_num
  have h1 : δ ^ loss * |Real.log δ| ^ D ≤ 1 / C := hcore δ hδ_pos hδ_lt_core
  have h2 : |Real.log δ| = Real.log (1 / δ) := by
    have h3 : Real.log δ < 0 := Real.log_neg hδ_pos (by linarith)
    have h4 : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div (by norm_num) (ne_of_gt hδ_pos), Real.log_one] <;> ring
    rw [abs_of_neg h3, h4] <;> ring
  rw [h2] at h1
  set L : ℝ := Real.log (1 / δ) with hL_def
  have hL_pos : 0 < L := by
    have h5 : 1 < 1 / δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h5
  have h3 : δ ^ loss * L ^ D ≤ 1 / C := h1
  have h4 : C * δ ^ loss * L ^ D ≤ 1 := by
    have h5 : C * (δ ^ loss * L ^ D) ≤ C * (1 / C) := by gcongr
    have h6 : C * (1 / C) = 1 := by field_simp [hC_pos.ne']
    rw [h6] at h5
    have h7 : C * δ ^ loss * L ^ D = C * (δ ^ loss * L ^ D) := by ring
    rw [h7]
    exact h5
  have h7 : 0 < δ ^ loss := by positivity
  have h8 : C * L ^ D ≤ δ ^ (-loss) := by
    have h9 : C * L ^ D = (C * δ ^ loss * L ^ D) / δ ^ loss := by
      field_simp [h7.ne'] <;> ring
    rw [h9]
    have h10 : (C * δ ^ loss * L ^ D) / δ ^ loss ≤ 1 / δ ^ loss := by gcongr
    have h11 : (1 : ℝ) / δ ^ loss = δ ^ (-loss) := by
      rw [Real.rpow_neg (le_of_lt hδ_pos)] <;> ring
    have h12 : (C * δ ^ loss * L ^ D) / δ ^ loss ≤ (1 : ℝ) / δ ^ loss := h10
    rw [h11] at h12
    exact h12
  exact h8

/-- Absorb a polylog LOWER bound factor: δ^loss ≤ C * log(1/δ)^{-D}.

    From polylog_absorption_core: δ^loss * |log δ|^D ≤ C
    ⇒ δ^loss ≤ C * log^{-D}.

    Requires loss > 0, D > 0. -/
lemma absorb_polylog_lower
    (C D loss : ℝ) (hC_pos : 0 < C) (hD_pos : 0 < D) (hloss_pos : 0 < loss) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      δ ^ loss ≤ C * (Real.log (1 / δ)) ^ (-D) := by
  rcases polylog_absorption_core loss D C hloss_pos hD_pos hC_pos with
    ⟨δ_core, hδ_core_pos, hcore⟩
  let δ₀ := min δ_core (1 / 2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
  have hδ_lt_core : δ < δ_core := by
    calc δ < δ₀ := hδ_lt
         _ ≤ δ_core := min_le_left _ _
  have hδ_lt_one : δ < 1 := by
    calc δ < δ₀ := hδ_lt
         _ ≤ 1 / 2 := min_le_right _ _
         _ < 1 := by norm_num
  have h1 : δ ^ loss * |Real.log δ| ^ D ≤ C := hcore δ hδ_pos hδ_lt_core
  have h2 : |Real.log δ| = Real.log (1 / δ) := by
    have h3 : Real.log δ < 0 := Real.log_neg hδ_pos (by linarith)
    have h4 : Real.log (1 / δ) = -Real.log δ := by
      rw [Real.log_div (by norm_num) (ne_of_gt hδ_pos), Real.log_one] <;> ring
    rw [abs_of_neg h3, h4] <;> ring
  rw [h2] at h1
  set L : ℝ := Real.log (1 / δ) with hL_def
  have hL_pos : 0 < L := by
    have h5 : 1 < 1 / δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h5
  have h3 : δ ^ loss * L ^ D ≤ C := h1
  have h4 : 0 < L ^ D := by positivity
  have h5 : δ ^ loss ≤ C * L ^ (-D) := by
    have h_eq : δ ^ loss = (δ ^ loss * L ^ D) / L ^ D := by
      field_simp [h4.ne'] <;> ring
    rw [h_eq]
    have h6 : (δ ^ loss * L ^ D) / L ^ D ≤ C / L ^ D := by gcongr
    have h7 : C / L ^ D = C * L ^ (-D) := by
      rw [Real.rpow_neg (by positivity)] <;> ring
    calc (δ ^ loss * L ^ D) / L ^ D
      ≤ C / L ^ D := h6
    _ = C * L ^ (-D) := h7
  exact h5

/-! ========================================================================
   Main exponent ledger theorem
   ======================================================================== -/

/-- Exponent ledger: common threshold and final bound.

    Given a loss ledger with both budgets closing, and polylog bounds on K and M,
    find a common δ0 such that for all δ < δ0, the coarse branch algebra gives
    N₀ ≥ δ^{-(2s+η)}.

    The data packages have retention losses baked in:
      coarseData.coarseGain = L.coarseGain
      fineData.localLoss = L.localLoss + L.fiber_L + L.b1_retention

    Regularity budget (checked separately): η + L.regularity_degradation ≤ L.εA
    Coarse branch budget: η ≤ coarseData.coarseGain - fineData.localLoss
                         - multiplicityLoss - loss_K - transfer_loss
-/
theorem exponent_ledger_final
    {s : ℝ} (hs_pos : 0 < s)
    (L : LossLedger s)
    (η : ℝ) (hη_pos : 0 < η)
    (h_regularity_budget : L.regularityBudget η)
    (h_coarse_budget : L.coarseBranchBudget η)
    -- Polylog bounds
    (C_K D_K : ℝ) (hC_K_pos : 0 < C_K) (hD_K_pos : 0 < D_K)
    (C_M D_M : ℝ) (hC_M_pos : 0 < C_M) (hD_M_pos : 0 < D_M)
    -- Strict positivity for absorption
    (hloss_K_pos : 0 < L.loss_K)
    (hmultiplicityLoss_pos : 0 < L.multiplicityLoss) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < δ₀ →
      ∀ (N₀ M K : ℕ)
        (coarseData : CoarseRatioData δ s)
        (fineData : FineCor25Data δ s)
        (hK_ge1 : 1 ≤ (K : ℝ))
        (hM_pos : 0 < (M : ℝ))
        (hK_bound : (K : ℝ) ≤ C_K * (Real.log (1 / δ)) ^ D_K)
        (hM_bound : (M : ℝ) ≥ C_M * δ ^ (-s) * (Real.log (1 / δ)) ^ (-D_M))
        (h_bridge : (K : ℝ) * (N₀ : ℝ) *
            coarseData.coarseMultiplicity * fineData.localMultiplicity ≥
          coarseData.coarseCount * fineData.localCount * (M : ℝ))
        (h_gain_match : coarseData.coarseGain = L.coarseGain)
        (h_loss_match : fineData.localLoss = L.localLoss + L.fiber_L + L.b1_retention),
        (N₀ : ENNReal) ≥ ENNReal.ofReal (δ ^ (-(2 * s + η))) := by
  -- Absorption for K
  rcases absorb_polylog_upper C_K D_K L.loss_K hC_K_pos hD_K_pos hloss_K_pos with
    ⟨δ_K, hδ_K_pos, h_abs_K⟩

  -- Absorption for M
  rcases absorb_polylog_lower C_M D_M L.multiplicityLoss hC_M_pos hD_M_pos hmultiplicityLoss_pos with
    ⟨δ_M, hδ_M_pos, h_abs_M⟩

  -- Common threshold: min of δ_K, δ_M, and 1/2
  let δ₀ := min δ_K (min δ_M (1 / 2))
  have hδ₀_pos : 0 < δ₀ := by positivity

  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
  intro N₀ M K coarseData fineData hK_ge1 hM_pos hK_bound hM_bound h_bridge
    h_gain_match h_loss_match

  have hδ_lt_K : δ < δ_K := by
    calc δ < δ₀ := hδ_lt
         _ ≤ δ_K := min_le_left _ _
  have hδ_lt_M : δ < δ_M := by
    calc δ < δ₀ := hδ_lt
         _ ≤ min δ_M (1 / 2) := min_le_right _ _
         _ ≤ δ_M := min_le_left _ _
  have hδ_lt_one : δ < 1 := by
    calc δ < δ₀ := hδ_lt
         _ ≤ min δ_M (1 / 2) := min_le_right _ _
         _ ≤ 1 / 2 := min_le_right _ _
         _ < 1 := by norm_num

  have h_abs_K' : C_K * (Real.log (1 / δ)) ^ D_K ≤ δ ^ (-L.loss_K) :=
    h_abs_K δ hδ_pos hδ_lt_K

  have h_abs_M' : δ ^ L.multiplicityLoss ≤ C_M * (Real.log (1 / δ)) ^ (-D_M) :=
    h_abs_M δ hδ_pos hδ_lt_M

  have hK_polylog : (K : ℝ) ≤ δ ^ (-L.loss_K) :=
    le_trans hK_bound h_abs_K'

  have hM_lower_base : (M : ℝ) ≥ δ ^ (-s + L.multiplicityLoss) := by
    calc (M : ℝ)
      ≥ C_M * δ ^ (-s) * (Real.log (1 / δ)) ^ (-D_M) := hM_bound
    _ = δ ^ (-s) * (C_M * (Real.log (1 / δ)) ^ (-D_M)) := by ring
    _ ≥ δ ^ (-s) * δ ^ L.multiplicityLoss := by gcongr
    _ = δ ^ (-s + L.multiplicityLoss) := by
      rw [←Real.rpow_add hδ_pos] <;> ring

  -- Weaken M bound to include transfer_loss in lambda slot
  -- Since δ < 1 and transfer_loss ≥ 0, δ^{-s+mult+transfer} ≤ δ^{-s+mult}
  have htransfer_nonneg : 0 ≤ L.transfer_loss := L.htransfer_loss_nonneg
  have hM_lower : (M : ℝ) ≥ δ ^ (-s + (L.multiplicityLoss + L.transfer_loss) + 0) := by
    have h9 : -s + (L.multiplicityLoss + L.transfer_loss) + 0 ≥ -s + L.multiplicityLoss := by linarith
    have h10 : δ ^ (-s + (L.multiplicityLoss + L.transfer_loss) + 0) ≤ δ ^ (-s + L.multiplicityLoss) := by
      exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h9
    exact le_trans h10 hM_lower_base

  -- Coarse branch budget algebra
  -- Map: lambda = multiplicityLoss + transfer_loss, rho_M = 0, loss_K = loss_K
  have h_budget_algebra : η ≤ coarseData.coarseGain - fineData.localLoss -
      (L.multiplicityLoss + L.transfer_loss) - 0 - L.loss_K := by
    rw [h_gain_match, h_loss_match]
    have h : η ≤ L.coarseBranchNetGain := h_coarse_budget
    dsimp only [LossLedger.coarseBranchNetGain, LossLedger.coarseBranchTotalLoss] at h
    linarith

  exact coarse_branch_algebra (lambda := L.multiplicityLoss + L.transfer_loss) (ρ_M := 0)
    coarseData fineData hK_ge1 hM_pos hM_lower hK_polylog
    h_bridge h_budget_algebra hδ_pos hδ_lt_one

/-- Fixed-δ version of the exponent ledger.

    Use this when the polylog absorptions have already been performed at
    the given δ (e.g., in step7 of the skeleton). Takes the absorbed
    bounds directly instead of constructing a threshold.

    This is the core algebra without the threshold-finding wrapper.
-/
lemma exponent_ledger_at_delta
    {s δ : ℝ} (hs_pos : 0 < s) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (L : LossLedger s) (η : ℝ) (hη_pos : 0 < η)
    (h_regularity_budget : L.regularityBudget η)
    (h_coarse_budget : L.coarseBranchBudget η)
    (N₀ M K : ℕ)
    (coarseData : CoarseRatioData δ s)
    (fineData : FineCor25Data δ s)
    (hK_ge1 : 1 ≤ (K : ℝ))
    (hM_pos : 0 < (M : ℝ))
    (hK_polylog : (K : ℝ) ≤ δ ^ (-L.loss_K))
    (hM_lower : (M : ℝ) ≥ δ ^ (-s + L.multiplicityLoss + L.transfer_loss))
    (h_bridge : (K : ℝ) * (N₀ : ℝ) *
        coarseData.coarseMultiplicity * fineData.localMultiplicity ≥
      coarseData.coarseCount * fineData.localCount * (M : ℝ))
    (h_gain_match : coarseData.coarseGain = L.coarseGain)
    (h_loss_match : fineData.localLoss = L.localLoss + L.fiber_L + L.b1_retention) :
    (N₀ : ENNReal) ≥ ENNReal.ofReal (δ ^ (-(2 * s + η))) := by
  have h_budget_algebra : η ≤ coarseData.coarseGain - fineData.localLoss -
      (L.multiplicityLoss + L.transfer_loss) - 0 - L.loss_K := by
    rw [h_gain_match, h_loss_match]
    have h : η ≤ L.coarseBranchNetGain := h_coarse_budget
    dsimp only [LossLedger.coarseBranchNetGain, LossLedger.coarseBranchTotalLoss] at h
    linarith
  have hM_lower' : (M : ℝ) ≥ δ ^ (-s + (L.multiplicityLoss + L.transfer_loss) + 0) := by
    have h_eq : -s + (L.multiplicityLoss + L.transfer_loss) + 0 = -s + L.multiplicityLoss + L.transfer_loss := by ring
    rw [h_eq]
    exact hM_lower
  exact coarse_branch_algebra (lambda := L.multiplicityLoss + L.transfer_loss) (ρ_M := 0)
    coarseData fineData hK_ge1 hM_pos hM_lower' hK_polylog
    h_bridge h_budget_algebra hδ_pos hδ_lt_one

/-! ========================================================================
   Budget documentation

   REGULARITY BUDGET (correct direction):
   - Start with S-set constant C = δ^{-εA} (from Appendix A hypothesis)
   - Each retention/thinning step MULTIPLIES C by K ≥ 1
   - Absorb K into exponent: C · K ≤ δ^{-(εA + loss)} for small δ
   - The exponent INCREASES: εA → εA + loss (constant worsens)
   - After all steps: C_final ≤ δ^{-(εA + regularity_degradation)}
   - To prove incidence exponent η, need: η + regularity_degradation ≤ εA
     (the retained set still satisfies the Appendix A S-set hypothesis)

   COARSE BRANCH BUDGET:
   - coarseGain from Appendix A coarse alternative (function of εA)
   - fineData.localLoss includes fiber_L and b1_retention
   - Additional explicit losses: multiplicityLoss, loss_K, transfer_loss
   - Condition: η ≤ coarseGain - localLoss - fiber_L - b1_retention
                              - multiplicityLoss - loss_K - transfer_loss

   Both budgets must close simultaneously.
-/

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
