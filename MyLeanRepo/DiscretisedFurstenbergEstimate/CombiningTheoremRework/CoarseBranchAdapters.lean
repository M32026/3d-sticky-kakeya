module

/-
  Coarse Branch Adapters

  Adapts the full B1ProductPackage and LossLedger from ExponentLedgerClean
  to the simplified interfaces expected by CoarseBranchAssemblyClean.

  Provides:
  1. `b1_polylog_threshold`: the δ0 threshold for K polynomial→polylog conversion
  2. `b1_product_to_simplified`: convert extracted B1 data to simplified B1ProductPackage
  3. `ledger_to_simplified`: convert full LossLedger to simplified LossLedger

  Whiteprint node: combining_theorem_rework / coarse_branch_adapters
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.ExponentLedgerClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.PowerBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAssemblyClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Section6

/-! ========================================================================
   B1ProductPackage adapter
   ======================================================================== -/

/-- The polylog absorption threshold for converting the polynomial K bound
    `K ≤ C * (4n+7)^7` into the power bound `K ≤ δ_n^{-loss_K}`.

    Use `b1_product_to_simplified` with the hypothesis
    `dyadicDelta n < b1_polylog_threshold loss_K hloss_K_pos`. -/
def b1_polylog_threshold (loss_K : ℝ) (hloss_K_pos : 0 < loss_K) : ℝ :=
  Classical.choose (polynomial7_absorption (2 * 2700 * 3145728) loss_K
    (by norm_num) hloss_K_pos)

/-- The threshold is positive and has the expected polylog absorption property. -/
lemma b1_polylog_threshold_spec (loss_K : ℝ) (hloss_K_pos : 0 < loss_K) :
    0 < b1_polylog_threshold loss_K hloss_K_pos ∧
    ∀ n : ℕ, 0 < n → dyadicDelta n < b1_polylog_threshold loss_K hloss_K_pos →
      ∀ X : ℝ, X ≤ (2 * 2700 * 3145728) * (4 * (n : ℝ) + 7)^7 →
        X ≤ (dyadicDelta n)^(-loss_K) :=
  Classical.choose_spec (polynomial7_absorption (2 * 2700 * 3145728) loss_K
    (by norm_num) hloss_K_pos)

/-- Construct a simplified `B1ProductPackage` from extracted B1 data.

    Requires `dyadicDelta n < b1_polylog_threshold loss_K hloss_K_pos` so that
    the polynomial K bound can be converted to a polylog power bound.

    The caller supplies `lambda`, `rho_M`, and the multiplicity lower bound `hM_lower`.
    Typical mapping from the full LossLedger:
      lambda = multiplicityLoss + transfer_loss
      rho_M = 0
      hM_lower : M ≥ δ_n^{-s + lambda + rho_M} -/
def b1_product_to_simplified
    {n : ℕ} (hn_pos : 0 < n)
    (s : ℝ)
    (K_nat N₀ M : ℕ)
    (hK_ge1 : 1 ≤ (K_nat : ℝ))
    (hM_pos : 0 < (M : ℝ))
    (hK_polynomial : (K_nat : ℝ) ≤ 2 * 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    (loss_K lambda rho_M : ℝ)
    (hloss_K_pos : 0 < loss_K)
    (hlambda_nonneg : 0 ≤ lambda)
    (hrho_M_nonneg : 0 ≤ rho_M)
    (hM_lower : (M : ℝ) ≥ (dyadicDelta n) ^ (-s + lambda + rho_M))
    (hδn_small : dyadicDelta n < b1_polylog_threshold loss_K hloss_K_pos) :
    B1ProductPackage (dyadicDelta n) s :=
  have h_abs : ∀ X : ℝ, X ≤ (2 * 2700 * 3145728) * (4 * (n : ℝ) + 7)^7 →
      X ≤ (dyadicDelta n)^(-loss_K) :=
    (b1_polylog_threshold_spec loss_K hloss_K_pos).2 n hn_pos hδn_small
  have hK_polylog : (K_nat : ℝ) ≤ (dyadicDelta n)^(-loss_K) :=
    h_abs (K_nat : ℝ) hK_polynomial
  {
    K := K_nat,
    N₀ := N₀,
    M := M,
    hK_ge1 := hK_ge1,
    hM_pos := hM_pos,
    loss_K := loss_K,
    hloss_K_nonneg := by linarith,
    hK_polylog := hK_polylog,
    lambda := lambda,
    hlambda_nonneg := hlambda_nonneg,
    rho_M := rho_M,
    hrho_M_nonneg := hrho_M_nonneg,
    hM_lower := hM_lower
  }

/-! ========================================================================
   LossLedger adapter
   ======================================================================== -/

/-- Construct a simplified `LossLedger` from the full `LossLedger`.

    Mapping:
    - simplified coarseGain = full coarseGain
    - simplified localLoss = full localLoss + fiber_L + b1_retention
    - netGain = full coarseBranchNetGain

    The budget inequality must hold with respect to the supplied `pkg`'s fields.
    When `pkg` is constructed with:
      pkg.lambda = ledger.multiplicityLoss + ledger.transfer_loss
      pkg.rho_M = 0
      pkg.loss_K = ledger.loss_K
    the budget is an equality and follows by `ring`. -/
def ledger_to_simplified {s : ℝ} (ledger : LossLedger s)
    (h_netGain_pos : 0 < ledger.coarseBranchNetGain)
    {δ : ℝ} {pkg : DirecretisedFurstenbergEstimate.Section6.B1ProductPackage δ s}
    (h_budget : ledger.coarseBranchNetGain ≤ ledger.coarseGain -
        (ledger.localLoss + ledger.fiber_L + ledger.b1_retention) -
        pkg.lambda - pkg.rho_M - pkg.loss_K) :
    DirecretisedFurstenbergEstimate.Section6.LossLedger
      ledger.coarseGain
      (ledger.localLoss + ledger.fiber_L + ledger.b1_retention)
      (pkg := pkg) :=
  {
    netGain := ledger.coarseBranchNetGain,
    hnetGain_pos := h_netGain_pos,
    h_budget := h_budget
  }

/-- Convenience: when the B1 package fields exactly match the LossLedger fields,
    the budget holds by definition (equality). -/
def ledger_to_simplified_of_match {s : ℝ} (ledger : LossLedger s)
    (h_netGain_pos : 0 < ledger.coarseBranchNetGain)
    {δ : ℝ} {pkg : DirecretisedFurstenbergEstimate.Section6.B1ProductPackage δ s}
    (h_lambda : pkg.lambda = ledger.multiplicityLoss + ledger.transfer_loss)
    (h_rho_M : pkg.rho_M = 0)
    (h_loss_K : pkg.loss_K = ledger.loss_K) :
    DirecretisedFurstenbergEstimate.Section6.LossLedger
      ledger.coarseGain
      (ledger.localLoss + ledger.fiber_L + ledger.b1_retention)
      (pkg := pkg) :=
  have h_eq : ledger.coarseBranchNetGain =
      ledger.coarseGain - (ledger.localLoss + ledger.fiber_L + ledger.b1_retention) -
      (ledger.multiplicityLoss + ledger.transfer_loss) - 0 - ledger.loss_K := by
    simp [LossLedger.coarseBranchNetGain, LossLedger.coarseBranchTotalLoss]
    <;> ring
  have h_budget : ledger.coarseBranchNetGain ≤ ledger.coarseGain -
      (ledger.localLoss + ledger.fiber_L + ledger.b1_retention) -
      pkg.lambda - pkg.rho_M - pkg.loss_K := by
    rw [h_lambda, h_rho_M, h_loss_K]
    exact h_eq.le
  ledger_to_simplified ledger h_netGain_pos h_budget

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
