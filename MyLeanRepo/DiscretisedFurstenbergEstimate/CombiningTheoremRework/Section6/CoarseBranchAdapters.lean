module

/-
  Coarse Branch Adapters — B1 Data to Assembly Inputs

  Provides adapters from B1InductionData to the structures consumed by
  coarse_branch_combination:

  1. `b1_product_package_from_data` — construct B1ProductPackage from B1InductionData
  2. `product_inequality_from_b1` — extract h_product for a specific coarse square
  3. `coarse_data_from_b1` — construct CoarseRatioData with honest geometry coefficient
  4. `construct_K_nat_bounds` — Nat.ceil data.K with all required bounds
  5. `K_nat_polynomial_bound` — polynomial bound for K_nat

  Whiteprint node: coarse_branch_adapters_section6
  Status: PRODUCTION
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAssemblyClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseRatioClean
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Section6

/-- Extract B1ProductPackage from B1InductionData.

    The caller supplies N₀ (the retained tube count, typically fineTubes.card),
    K_nat (a natural number overhead bounding data.K), exponent parameters,
    and the polylog threshold. -/
def b1_product_package_from_data
    {n m : ℕ} (hn_pos : 0 < n) (hnm : m ≤ n)
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : B1InductionData n m hnm s t C₁ M config)
    (hM_pos : 0 < M)
    -- N₀: retained tube count (typically fineTubesOfData data).card
    (N₀ : ℕ)
    -- Exponent parameters for B1ProductPackage
    (loss_K lambda rho_M : ℝ)
    (hloss_K_pos : 0 < loss_K)
    (hlambda_nonneg : 0 ≤ lambda)
    (hrho_M_nonneg : 0 ≤ rho_M)
    -- Multiplicity lower bound: M ≥ δ_n^{-s + lambda + rho_M}
    (hM_lower : (M : ℝ) ≥ (dyadicDelta n) ^ (-s + lambda + rho_M))
    -- K_nat: natural number overhead
    (K_nat : ℕ)
    (hK_nat_ge1 : 1 ≤ (K_nat : ℝ))
    (hK_nat_bound : (K_nat : ℝ) ≤ 2 * 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    -- δ_n small enough for polylog absorption
    (hδn_small : dyadicDelta n < b1_polylog_threshold loss_K hloss_K_pos) :
    B1ProductPackage (dyadicDelta n) s :=
  b1_product_to_simplified
    (hn_pos := hn_pos)
    (s := s)
    (K_nat := K_nat)
    (N₀ := N₀)
    (M := M)
    (hK_ge1 := hK_nat_ge1)
    (hM_pos := by exact_mod_cast hM_pos)
    (hK_polynomial := hK_nat_bound)
    (loss_K := loss_K)
    (lambda := lambda)
    (rho_M := rho_M)
    (hloss_K_pos := hloss_K_pos)
    (hlambda_nonneg := hlambda_nonneg)
    (hrho_M_nonneg := hrho_M_nonneg)
    (hM_lower := hM_lower)
    (hδn_small := hδn_small)

/-- Extract the product inequality for a specific coarse square Q.

    From b1_bridge_data_helper's raw product, weakens the real overhead
    `data.K` to a natural number `K_nat` satisfying `data.K ≤ K_nat`
    (typically `K_nat = Nat.ceil data.K`).

    Since all other factors are nonnegative:
      data.K * N₀ * MΔ * MQ ≤ K_nat * N₀ * MΔ * MQ
    So the raw product `data.K * ... ≥ NΔ * NQ * M` implies
    `K_nat * ... ≥ NΔ * NQ * M`. -/
lemma product_inequality_from_b1
    {n m : ℕ} (hnm : m ≤ n)
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : B1InductionData n m hnm s t C₁ M config)
    (N₀ : ℕ)
    (K_nat : ℕ)
    (hK_nat_ge_K : (data.K : ℝ) ≤ (K_nat : ℝ))
    (h_raw_product : ∀ Q hQ, (data.K : ℝ) * (N₀ : ℝ) *
        (data.MΔ : ℝ) * (data.MQ Q : ℝ) ≥
      (data.coarseConfig.T₀.card : ℝ) *
        ((data.fineConfig Q hQ).T₀.card : ℝ) * (M : ℝ))
    (Q : DyadicSquare m)
    (hQ : Q ∈ data.coarseConfig.P₀) :
    (K_nat : ℝ) * (N₀ : ℝ) *
      (data.MΔ : ℝ) * (data.MQ Q : ℝ) ≥
    (data.coarseConfig.T₀.card : ℝ) *
      ((data.fineConfig Q hQ).T₀.card : ℝ) * (M : ℝ) := by
  have h_raw := h_raw_product Q hQ
  have hN0_nonneg : 0 ≤ (N₀ : ℝ) := by positivity
  have hMΔ_nonneg : 0 ≤ (data.MΔ : ℝ) := by positivity
  have hMQ_nonneg : 0 ≤ (data.MQ Q : ℝ) := by positivity
  have h_weaken : (data.K : ℝ) * (N₀ : ℝ) * (data.MΔ : ℝ) * (data.MQ Q : ℝ) ≤
      (K_nat : ℝ) * (N₀ : ℝ) * (data.MΔ : ℝ) * (data.MQ Q : ℝ) := by
    gcongr
    <;> linarith
  exact le_trans h_raw h_weaken

/-- Construct CoarseRatioData from B1 data with honest geometry coefficient.

    The honest Appendix A coarse bound has a geometry coefficient:
      NΔ ≥ C_geo * δ_n^{-(s+εA)}
    where C_geo = 262144^{-2} * 9^{-(s+εA)} (from covering chain).

    This adapter absorbs C_geo into a `loss_parent` exponent:
      C_geo ≥ δ_n^{loss_parent}
    ⟹ NΔ ≥ δ_n^{-(s+εA)} * δ_n^{loss_parent} = δ_n^{-(s+εA-loss_parent)}

    Then calls `coarse_ratio_producer` with effective ε = εA - loss_parent.

    IMPORTANT: `loss_parent` charges the geometry coefficient exactly ONCE.
    The separate `loss` parameter absorbs only the Cor 2.5/Prop 5 polylog
    coefficient — do not include 262144² or 9 factors there again. -/
def coarse_data_from_b1
    {n m : ℕ} (hn_pos : 0 < n)
    {s u0 εA C_prop5 loss_parent loss : ℝ}
    {NΔ MΔ : ℝ}
    -- Scale
    (hδn_pos : 0 < dyadicDelta n)
    (hδn_one : dyadicDelta n ≤ 1)
    (hδm_pos : 0 < dyadicDelta m)
    (hδm_one : dyadicDelta m < 1)
    (h_even : n = 2 * m)
    -- Dimension
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsu : s < u0) (hu0_one : u0 ≤ 1)
    -- Appendix A gain
    (hεA_pos : 0 < εA)
    -- Geometry coefficient (e.g. 262144^{-2} * 9^{-(s+εA)})
    (C_geo : ℝ)
    (hC_geo_pos : 0 < C_geo)
    (h_loss_parent_nonneg : 0 ≤ loss_parent)
    (h_loss_parent_lt_εA : loss_parent < εA)
    -- Absorb geometry coefficient into exponent loss
    (h_absorb_geo : C_geo ≥ (dyadicDelta n) ^ loss_parent)
    -- Honest coarse bound with coefficient
    (hNΔ_nonneg : 0 ≤ NΔ)
    (hMΔ_pos : 0 < MΔ)
    (h_coarse_bound_geo : NΔ ≥ C_geo * (dyadicDelta n) ^ (-(s + εA)))
    -- Effective Cor 2.5 / Prop 5 bound (polylog coefficient separate)
    (hC_prop5_pos : 0 < C_prop5)
    (α : ℝ)
    (hα_def : α = (u0 - s) / (1 - s))
    (h_prop5 : NΔ ≥ C_prop5 * MΔ * (dyadicDelta m)^(-s) * (MΔ * (dyadicDelta m)^s)^α)
    -- Polylog absorption for C_prop5 ONLY (not geometry)
    (hloss_nonneg : 0 ≤ loss)
    (h_absorb_prop5 : C_prop5 ≥ (dyadicDelta n)^loss)
    (hloss_small : loss < (εA - loss_parent) * α / 2) :
    CoarseRatioData (dyadicDelta n) s :=
  have hδ_eq2 : dyadicDelta n = (dyadicDelta m) ^ 2 := by
    rw [h_even]
    have h4 : ∀ k : ℕ, (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      intro k
      have h5 : (4 : ℝ) ^ k = ((2 : ℝ) ^ 2) ^ k := by norm_num
      rw [h5, ← pow_mul] <;> ring
    simp [dyadicDelta, h4] <;> ring
  have hε_eff_pos : 0 < εA - loss_parent := by linarith
  have h_coarse_bound : NΔ ≥ (dyadicDelta n) ^ (-(s + (εA - loss_parent))) := by
    have h1 : NΔ ≥ C_geo * (dyadicDelta n) ^ (-(s + εA)) := h_coarse_bound_geo
    have h2 : C_geo * (dyadicDelta n) ^ (-(s + εA)) ≥
        (dyadicDelta n) ^ loss_parent * (dyadicDelta n) ^ (-(s + εA)) := by
      gcongr
      <;> linarith
    have h3 : (dyadicDelta n) ^ loss_parent * (dyadicDelta n) ^ (-(s + εA)) =
        (dyadicDelta n) ^ (-(s + (εA - loss_parent))) := by
      rw [← Real.rpow_add hδn_pos]
      <;> ring_nf
    rw [h3] at h2
    exact le_trans h2 h1
  coarse_ratio_producer
    (hδ_pos := hδn_pos)
    (hδ_one := hδn_one)
    (hΔ_pos := hδm_pos)
    (hΔ_one := hδm_one)
    (hδ_eq2 := hδ_eq2)
    (hs := hs_pos)
    (hs1 := hs_lt_one)
    (hsu := hsu)
    (hu0_one := hu0_one)
    (hε_pos := hε_eff_pos)
    (hNΔ_nonneg := hNΔ_nonneg)
    (hMΔ_pos := hMΔ_pos)
    (h_coarse_bound := h_coarse_bound)
    (hC_prop5_pos := hC_prop5_pos)
    (α := α)
    (hα_def := hα_def)
    (h_prop5 := h_prop5)
    (hloss_pos := hloss_nonneg)
    (h_absorb := h_absorb_prop5)
    (hloss_small := hloss_small)

/-- Construct K_nat := Nat.ceil data.K with all required bounds.

    Given data.K ≥ 1:
    - K_nat ≥ 1
    - data.K ≤ K_nat
    - K_nat ≤ 2 * data.K
-/
lemma construct_K_nat_bounds
    {n m : ℕ} {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (hnm : m ≤ n)
    (data : B1InductionData n m hnm s t C₁ M config)
    (K_nat : ℕ)
    (hK_nat_def : K_nat = Nat.ceil data.K) :
    1 ≤ (K_nat : ℝ) ∧
    (data.K : ℝ) ≤ (K_nat : ℝ) ∧
    (K_nat : ℝ) ≤ 2 * data.K := by
  have hK_ge1 : 1 ≤ data.K := data.hK_ge1
  set c : ℕ := Nat.ceil data.K with hc_def
  have hc_pos : 0 < c := by
    have h1 : (1 : ℝ) ≤ data.K := hK_ge1
    have h2 : (1 : ℝ) ≤ (c : ℝ) := le_trans h1 (Nat.le_ceil data.K)
    exact_mod_cast h2
  have h1 : (c : ℝ) ≤ data.K + 1 := by
    have h3 : ¬(data.K ≤ ↑(c - 1)) := by
      intro h4
      have h5 : c ≤ c - 1 := Nat.ceil_le.mpr h4
      omega
    have h6 : data.K > ↑(c - 1) := by linarith
    have h7 : (↑(c - 1) : ℝ) = (c : ℝ) - 1 := by
      simp [hc_pos] <;> omega
    rw [h7] at h6
    linarith
  have h2 : (c : ℝ) ≤ 2 * data.K := by linarith [hK_ge1]
  have hK_nat_eq : (K_nat : ℝ) = (c : ℝ) := by
    exact_mod_cast hK_nat_def
  rw [hK_nat_eq]
  exact ⟨by exact_mod_cast hc_pos, Nat.le_ceil data.K, h2⟩

/-- Polynomial bound for K_nat: if K ≤ C * (4n+7)^7,
    then K_nat ≤ 2C * (4n+7)^7. -/
lemma K_nat_polynomial_bound
    {n : ℕ} {C : ℝ} (K : ℝ) (K_nat : ℕ)
    (hK_nat_def : K_nat = Nat.ceil K)
    (hK_bound : K ≤ C * (4 * (n : ℝ) + 7)^7)
    (hC_pos : 0 < C)
    (hK_ge1 : 1 ≤ K) :
    (K_nat : ℝ) ≤ 2 * C * (4 * (n : ℝ) + 7)^7 := by
  set c : ℕ := Nat.ceil K with hc_def
  have hc_pos : 0 < c := by
    have h1 : (1 : ℝ) ≤ K := hK_ge1
    have h2 : (1 : ℝ) ≤ (c : ℝ) := le_trans h1 (Nat.le_ceil K)
    exact_mod_cast h2
  have h1 : (c : ℝ) ≤ K + 1 := by
    have h3 : ¬(K ≤ ↑(c - 1)) := by
      intro h4
      have h5 : c ≤ c - 1 := Nat.ceil_le.mpr h4
      omega
    have h6 : K > ↑(c - 1) := by linarith
    have h7 : (↑(c - 1) : ℝ) = (c : ℝ) - 1 := by
      simp [hc_pos] <;> omega
    rw [h7] at h6
    linarith
  have h2 : (c : ℝ) ≤ 2 * K := by linarith [hK_ge1]
  have hK_nat_eq : (K_nat : ℝ) = (c : ℝ) := by exact_mod_cast hK_nat_def
  rw [hK_nat_eq]
  calc (c : ℝ)
    ≤ 2 * K := h2
  _ ≤ 2 * (C * (4 * (n : ℝ) + 7)^7) := by gcongr
  _ = 2 * C * (4 * (n : ℝ) + 7)^7 := by ring

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
