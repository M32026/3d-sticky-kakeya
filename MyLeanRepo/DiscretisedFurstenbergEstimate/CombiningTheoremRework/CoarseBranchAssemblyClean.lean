module

/-
  Coarse Branch Assembly Lemma (Step 7)

  Assembles the coarse branch of Theorem 6.1:
  1. CoarseRatioData (from coarse_two_case_ratio + Appendix A coarse bound)
  2. FineCor25Data (from fine normalized Cor 2.5 ratio — indigo, placeholder)
  3. B1 product inequality (from b1_bridge_decomposition)
  4. Exponent budget (from LossLedger — juniper)

  Produces: original tube count N₀ ≥ δ_n^{-(2s + netGain)}

  This is a thin wrapper around `coarse_branch_algebra` that packages the
  B1 overhead K, original multiplicity M, and product inequality into a
  structured interface, and computes the exponent budget from a LossLedger.

  Whiteprint node: combining_theorem_rework / coarse_branch_assembly
  Status: Core algebra complete; FineCor25Data production is placeholder.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAlgebra
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.SourceFacingTheorem61

/-- B1 product package: overhead K, original count N₀, multiplicity M,
    and their respective bounds.

    The product inequality is passed separately to `coarse_branch_assembly`
    because it references CoarseRatioData and FineCor25Data.

    TODO: Replace with bacon's `B1NormalizedProductPackage` when available. -/
structure B1ProductPackage (δ s : ℝ) where
  K : ℕ
  N₀ : ℕ
  M : ℕ
  hK_ge1 : 1 ≤ (K : ℝ)
  hM_pos : 0 < (M : ℝ)
  -- Polylog bound: K ≤ δ^{-loss_K}
  loss_K : ℝ
  hloss_K_nonneg : 0 ≤ loss_K
  hK_polylog : (K : ℝ) ≤ δ ^ (-loss_K)
  -- Original multiplicity lower bound: M ≥ δ^{-s + lambda + rho_M}
  lambda : ℝ
  hlambda_nonneg : 0 ≤ lambda
  rho_M : ℝ
  hrho_M_nonneg : 0 ≤ rho_M
  hM_lower : (M : ℝ) ≥ δ ^ (-s + lambda + rho_M)

/-- Loss ledger for the coarse branch exponent budget.

    Given coarseGain, localLoss, and a B1ProductPackage, computes the
    net gain budget.

    TODO: Replace with juniper's `LossLedger` when available. -/
structure LossLedger (coarseGain localLoss : ℝ) {δ s : ℝ}
    (pkg : B1ProductPackage δ s) where
  netGain : ℝ
  hnetGain_pos : 0 < netGain
  -- Budget: netGain ≤ coarseGain - localLoss - pkg.lambda - pkg.rho_M - pkg.loss_K
  h_budget : netGain ≤ coarseGain - localLoss - pkg.lambda - pkg.rho_M - pkg.loss_K

/-- Coarse branch assembly: from ratio data + B1 product + loss ledger,
    prove the original tube count lower bound.

    This is the key step 7 lemma. Given:
    - CoarseRatioData (NΔ/MΔ ≥ δ^{-(s/2 + coarseGain)})
    - FineCor25Data (NQ/MQ ≥ δ^{-(s/2 - localLoss)})
    - B1ProductPackage (K, N₀, M, bounds)
    - Product inequality: K * N₀ * MΔ * MQ ≥ NΔ * NQ * M
    - LossLedger (netGain budget)

    Concludes: (N₀ : ENNReal) ≥ δ^{-(2s + netGain)}.
-/
lemma coarse_branch_assembly
    {δ s : ℝ}
    (coarseData : CoarseRatioData δ s)
    (fineData : FineCor25Data δ s)
    (pkg : B1ProductPackage δ s)
    (h_product : (pkg.K : ℝ) * (pkg.N₀ : ℝ) *
        coarseData.coarseMultiplicity * fineData.localMultiplicity ≥
      coarseData.coarseCount * fineData.localCount * (pkg.M : ℝ))
    (ledger : LossLedger coarseData.coarseGain fineData.localLoss pkg)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    (pkg.N₀ : ENNReal) ≥ ENNReal.ofReal (δ ^ (-(2 * s + ledger.netGain))) :=
  coarse_branch_algebra
    (coarseData := coarseData)
    (fineData := fineData)
    (hK_ge1 := pkg.hK_ge1)
    (hM_pos := pkg.hM_pos)
    (hM_lower := pkg.hM_lower)
    (hK_polylog := pkg.hK_polylog)
    (h_bridge := h_product)
    (h_budget := ledger.h_budget)
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)

/-- Dyadic-scale version: uses dyadicDelta n instead of arbitrary δ.

    Requires 0 < n so that dyadicDelta n < 1. -/
lemma coarse_branch_assembly_dyadic
    {n : ℕ} {s : ℝ}
    (hn_pos : 0 < n)
    (coarseData : CoarseRatioData (DiscretisedFurstenbergEstimate.dyadicDelta n) s)
    (fineData : FineCor25Data (DiscretisedFurstenbergEstimate.dyadicDelta n) s)
    (pkg : B1ProductPackage (DiscretisedFurstenbergEstimate.dyadicDelta n) s)
    (h_product : (pkg.K : ℝ) * (pkg.N₀ : ℝ) *
        coarseData.coarseMultiplicity * fineData.localMultiplicity ≥
      coarseData.coarseCount * fineData.localCount * (pkg.M : ℝ))
    (ledger : LossLedger coarseData.coarseGain fineData.localLoss pkg) :
    (pkg.N₀ : ENNReal) ≥
      ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta n) ^
        (-(2 * s + ledger.netGain))) :=
  let δn := DiscretisedFurstenbergEstimate.dyadicDelta n
  have hδ_pos : 0 < δn := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have hδ_lt_one : δn < 1 := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ n := by
      have h2 : ∀ k : ℕ, 0 < k → (1 : ℝ) < (2 : ℝ) ^ k := by
        intro k hk
        induction' hk with k hk ih
        · norm_num
        · simp [pow_succ] at * <;> linarith
      exact h2 n hn_pos
    have h2 : δn = 1 / (2 : ℝ) ^ n := by
      simp [δn, DiscretisedFurstenbergEstimate.dyadicDelta]
      <;> rfl
    rw [h2]
    have h3 : 1 / (2 : ℝ) ^ n < 1 := by
      apply (div_lt_one (by positivity)).mpr
      exact h1
    exact h3
  coarse_branch_assembly coarseData fineData pkg h_product ledger hδ_pos hδ_lt_one

end DirecretisedFurstenbergEstimate.Section6

end
