module

/-
  Coarse Branch from B1 Data — Source-Facing Integration

  Takes B1InductionData + Appendix A coarse outcome + selector facts and
  produces the final Ncover lower bound via coarse_branch_combination.

  Alpha accounting (critical):
  - Selector uses α_base = (min(t,1) - s) / (1 - s) for coarseGain_raw
  - Actual coarse data uses α_actual = (u0 - s) / (1 - s), u0 = min(u,1)
  - Since t ≤ u, α_base ≤ α_actual (alpha monotonicity)
  - This lets us upgrade the selector budget to the actual coarse gain:
      coarseData.coarseGain = (εA - loss_parent) * α_actual / 2 - loss_coarse
                           ≥ coarseGain_raw - loss_parent

  Loss budget uses ACTUAL coarseData.coarseGain (not raw gain).
  pkg.loss_K = loss_B1 ONLY — parent loss is in coarseGain, not double-counted.

  Whiteprint node: coarse_branch_from_b1_data
  Status: DRAFT
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CoarseBranchAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CoarseBranchCombination
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.CoarseBranchAdapters
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.FixedPackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.AlphaMonotonicity
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Section6
open DirecretisedFurstenbergEstimate.RegularIncidence (S0_line)
open DyadicCardToNcover (toAffineLine)
open DirecretisedFurstenbergEstimate.FixedPackingBound (C_pack)

/-- Source-facing coarse branch: from B1 induction data + Appendix A outcome +
    selector facts, prove the original family Ncover lower bound.

    Generalized interface: the caller provides `N₀` and `fineTubes` explicitly,
    along with `h_fineTubes_card : fineTubes.card = N₀`. This allows using either
    the B1-retained tube family (`fineTubesOfData data`) or the full config T₀,
    depending on which product inequality and provenance bounds are available.

    Uses alpha monotonicity: selector's α_base ≤ actual α_actual because t ≤ u
    and u0 = min(u,1). The selector budget based on α_base is conservative. -/
lemma coarse_branch_from_b1_data
    {n m : ℕ} (hn_pos : 0 < n) (hm_pos : 0 < m) (hnm : m ≤ n)
    {s t u εA εInc C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : B1InductionData n m hnm s t C₁ M config)
    -- Dimension / parameter conditions
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hst : s < t) (htu : t ≤ u)
    (hεA_pos : 0 < εA)
    (hεInc_pos : 0 < εInc)
    (hM_pos : 0 < M)
    -- Scale
    {δ : ℝ} (hδ_pos : 0 < δ)
    (h_even : n = 2 * m)
    (h_scale : dyadicDelta n ≤ δ / 4)
    (h_scale2 : δ / 4 < 4 * dyadicDelta n)
    -- Selected coarse square Q
    (Q : DyadicSquare m)
    (hQ : Q ∈ data.coarseConfig.P₀)
    -- K_nat polynomial bound
    (hK_nat_bound : (Nat.ceil data.K : ℝ) ≤ 2 * 2700 * 3145728 * (4 * (n : ℝ) + 7)^7)
    -- B1 product package exponent parameters
    (lambda rho_M loss_B1 : ℝ)
    (hloss_B1_pos : 0 < loss_B1)
    (hlambda_nonneg : 0 ≤ lambda)
    (hrho_M_nonneg : 0 ≤ rho_M)
    -- Frontend multiplicity bound + selector inequality
    (εReg fixedLoss : ℝ)
    (hεReg_nonneg : 0 ≤ εReg)
    (hfixedLoss_nonneg : 0 ≤ fixedLoss)
    (hM_lower_frontend : (M : ℝ) ≥ (dyadicDelta n) ^ (-s + εReg + fixedLoss))
    (hselector_budget_M : εReg + fixedLoss ≤ lambda + rho_M)
    (hδn_small : dyadicDelta n < b1_polylog_threshold loss_B1 hloss_B1_pos)
    -- Appendix A coarse bound with geometry coefficient
    (C_geo : ℝ) (hC_geo_pos : 0 < C_geo)
    (loss_parent : ℝ) (h_loss_parent_nonneg : 0 ≤ loss_parent)
    (h_loss_parent_lt_εA : loss_parent < εA)
    (h_absorb_geo : C_geo ≥ (dyadicDelta n) ^ loss_parent)
    (h_coarse_bound_geo : (data.coarseConfig.T₀.card : ℝ) ≥ C_geo * (dyadicDelta n) ^ (-(s + εA)))
    -- u0 cap and alpha parameters
    (u0 : ℝ) (hu0_def : u0 = min u 1)
    (α_base α_actual : ℝ)
    (hα_base_def : α_base = (min t 1 - s) / (1 - s))
    (hα_actual_def : α_actual = (u0 - s) / (1 - s))
    -- Prop 5 / Cor 2.5 bound for coarse config (uses α_actual)
    (C_prop5 : ℝ) (hC_prop5_pos : 0 < C_prop5)
    (h_prop5 : (data.coarseConfig.T₀.card : ℝ) ≥ C_prop5 * (data.MΔ : ℝ) *
        (dyadicDelta m)^(-s) * ((data.MΔ : ℝ) * (dyadicDelta m)^s)^α_actual)
    -- Coarse polylog absorption loss (DISTINCT from loss_parent)
    (loss_coarse : ℝ) (hloss_coarse_nonneg : 0 ≤ loss_coarse)
    (h_absorb_prop5 : C_prop5 ≥ (dyadicDelta n)^loss_coarse)
    (hloss_coarse_small : loss_coarse < (εA - loss_parent) * α_actual / 2)
    (hloss_coarse_le_half : loss_coarse ≤ loss_parent / 2)
    -- Selector gain budget (uses α_base, NOT α_actual)
    (coarseGain_raw localLoss netGain : ℝ)
    (h_coarseGain_raw_def : coarseGain_raw = εA * α_base / 2)
    (h_selector_budget : netGain ≤ coarseGain_raw - localLoss - lambda - rho_M - loss_B1 - loss_parent)
    (h_netGain_pos : 0 < netGain)
    -- FineCor25Data for selected Q
    (fineData : FineCor25Data (dyadicDelta n) s)
    (hfine_count : fineData.localCount = ((data.fineConfig Q hQ).T₀.card : ℝ))
    (hfine_mult : fineData.localMultiplicity = (data.MQ Q : ℝ))
    (hfine_loss : fineData.localLoss ≤ localLoss)
    -- Tube family for provenance + product count (caller chooses)
    (N₀ : ℕ)
    (fineTubes : Finset (DyadicTube n))
    (h_fineTubes_card : fineTubes.card = N₀)
    -- Raw product inequality from B1 bridge (uses N₀)
    (h_raw_product : ∀ Q' hQ', (data.K : ℝ) * (N₀ : ℝ) *
        (data.MΔ : ℝ) * (data.MQ Q' : ℝ) ≥
      (data.coarseConfig.T₀.card : ℝ) *
        ((data.fineConfig Q' hQ').T₀.card : ℝ) * (M : ℝ))
    -- Geometry bounds for fineTubes
    (hm : ∀ T ∈ fineTubes, |T.slope| ≤ 1)
    (hb : ∀ T ∈ fineTubes, |T.intercept| ≤ 3)
    -- Original family and provenance
    {originalFamily : Set DirecretisedFurstenbergEstimate.AffineLine}
    (h_thick : ∀ (T : DyadicTube n), T ∈ fineTubes →
        ∃ (ℓ : DirecretisedFurstenbergEstimate.AffineLine), ℓ ∈ originalFamily ∧
          dist (toAffineLine T) (S0_line ℓ) ≤ (15 / 2 : ℝ) * (δ / 4))
    -- Absorption: bridges δn^{-(2s+netGain)} / C_pack ≥ δ^{-(2s+εInc)}
    (h_absorb : ENNReal.ofReal (δ ^ (-(2 * s + εInc))) ≤
        ENNReal.ofReal ((dyadicDelta n) ^ (-(2 * s + netGain))) / (C_pack : ENNReal)) :
    ENNReal.ofReal (δ ^ (-(2 * s + εInc))) ≤
      DirecretisedFurstenbergEstimate.Section6.Ncover' δ originalFamily := by
  let δn := dyadicDelta n
  let δm := dyadicDelta m
  have hδn_pos : 0 < δn := dyadicDelta_pos n
  have hδn_one : δn ≤ 1 := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ n := by
      have h2 : ∀ k : ℕ, 0 < k → (1 : ℝ) < (2 : ℝ) ^ k := by
        intro k hk
        induction' hk with k hk ih
        · norm_num
        · simp [pow_succ] at * <;> linarith
      exact h2 n hn_pos
    have h3 : δn = 1 / (2 : ℝ) ^ n := by rfl
    rw [h3]
    have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ n := by linarith
    exact (div_le_one (by positivity)).mpr h4
  have hδm_pos : 0 < δm := dyadicDelta_pos m
  have hδm_one : δm < 1 := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ m := by
      have h2 : ∀ k : ℕ, 0 < k → (1 : ℝ) < (2 : ℝ) ^ k := by
        intro k hk
        induction' hk with k hk ih
        · norm_num
        · simp [pow_succ] at * <;> linarith
      exact h2 m hm_pos
    have h4 : δm = 1 / (2 : ℝ) ^ m := by rfl
    rw [h4]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hδn_lt_one : δn < 1 := by
    have h1 : (1 : ℝ) < (2 : ℝ) ^ n := by
      have h2 : ∀ k : ℕ, 0 < k → (1 : ℝ) < (2 : ℝ) ^ k := by
        intro k hk
        induction' hk with k hk ih
        · norm_num
        · simp [pow_succ] at * <;> linarith
      exact h2 n hn_pos
    have h3 : δn = 1 / (2 : ℝ) ^ n := by rfl
    rw [h3]
    apply (div_lt_one (by positivity)).mpr
    linarith

  -- Step 0: Alpha monotonicity — α_base ≤ α_actual
  have h_u0_le_one : u0 ≤ 1 := by
    rw [hu0_def]
    exact min_le_right _ _
  have h_s_lt_u0 : s < u0 := by
    rw [hu0_def]
    have h1 : s < min t 1 := lt_min hst hs_lt_one
    have h2 : min t 1 ≤ min u 1 := by gcongr <;> linarith
    linarith
  have hα_base_le_actual : α_base ≤ α_actual := by
    rw [hα_base_def, hα_actual_def, hu0_def]
    exact alpha_monotonicity s t u hs_pos hs_lt_one hst htu
  have hα_actual_le_one : α_actual ≤ 1 := by
    rw [hα_actual_def]
    have h1 : u0 - s ≤ 1 - s := by linarith
    have h2 : 0 < 1 - s := by linarith
    have h3 : (u0 - s) / (1 - s) ≤ (1 - s) / (1 - s) := by gcongr <;> linarith
    have h4 : (1 - s) / (1 - s) = 1 := by
      field_simp [h2.ne'] <;> ring
    rw [h4] at h3
    exact h3

  let K_nat : ℕ := Nat.ceil data.K

  -- Step 1: K_nat bounds
  have hK_bounds := construct_K_nat_bounds hnm data K_nat rfl
  have hK_nat_ge1 : 1 ≤ (K_nat : ℝ) := hK_bounds.1
  have hK_nat_ge_K : (data.K : ℝ) ≤ (K_nat : ℝ) := hK_bounds.2.1

  -- Step 2: Derive hM_lower for B1ProductPackage
  have h_exp_le : -s + εReg + fixedLoss ≤ -s + lambda + rho_M := by linarith
  have h_rpow_mon : δn ^ (-s + lambda + rho_M) ≤ δn ^ (-s + εReg + fixedLoss) :=
    Real.rpow_le_rpow_of_exponent_ge hδn_pos hδn_lt_one.le h_exp_le
  have hM_lower : (M : ℝ) ≥ δn ^ (-s + lambda + rho_M) :=
    le_trans h_rpow_mon hM_lower_frontend

  -- Step 3: Construct B1ProductPackage
  let pkg : B1ProductPackage δn s :=
    b1_product_package_from_data
      (hn_pos := hn_pos) (hnm := hnm)
      (data := data) (hM_pos := hM_pos)
      (N₀ := N₀)
      (loss_K := loss_B1) (lambda := lambda) (rho_M := rho_M)
      (hloss_K_pos := hloss_B1_pos)
      (hlambda_nonneg := hlambda_nonneg)
      (hrho_M_nonneg := hrho_M_nonneg)
      (hM_lower := hM_lower)
      (K_nat := K_nat)
      (hK_nat_ge1 := hK_nat_ge1)
      (hK_nat_bound := hK_nat_bound)
      (hδn_small := hδn_small)

  -- Step 4: Construct CoarseRatioData (uses α_actual)
  let NΔ : ℝ := (data.coarseConfig.T₀.card : ℝ)
  let MΔ : ℝ := (data.MΔ : ℝ)
  have hNΔ_nonneg : 0 ≤ NΔ := by positivity
  have hMΔ_pos : 0 < MΔ := by
    dsimp only [MΔ]
    have h : (0 : ℝ) < (data.MΔ : ℝ) := by exact_mod_cast data.hMΔ_pos
    exact h

  let coarseData : CoarseRatioData δn s :=
    coarse_data_from_b1
      (hn_pos := hn_pos)
      (hδn_pos := hδn_pos) (hδn_one := hδn_one)
      (hδm_pos := hδm_pos) (hδm_one := hδm_one)
      (h_even := h_even)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
      (hsu := h_s_lt_u0) (hu0_one := h_u0_le_one)
      (hεA_pos := hεA_pos)
      (C_geo := C_geo) (hC_geo_pos := hC_geo_pos)
      (loss_parent := loss_parent)
      (h_loss_parent_nonneg := h_loss_parent_nonneg)
      (h_loss_parent_lt_εA := h_loss_parent_lt_εA)
      (h_absorb_geo := h_absorb_geo)
      (hNΔ_nonneg := hNΔ_nonneg)
      (hMΔ_pos := hMΔ_pos)
      (h_coarse_bound_geo := h_coarse_bound_geo)
      (hC_prop5_pos := hC_prop5_pos)
      (α := α_actual) (hα_def := hα_actual_def)
      (h_prop5 := h_prop5)
      (loss := loss_coarse) (hloss_nonneg := hloss_coarse_nonneg)
      (h_absorb_prop5 := h_absorb_prop5)
      (hloss_small := hloss_coarse_small)

  -- Step 5: Product inequality for selected Q
  have h_product : (pkg.K : ℝ) * (pkg.N₀ : ℝ) *
      coarseData.coarseMultiplicity * fineData.localMultiplicity ≥
    coarseData.coarseCount * fineData.localCount * (pkg.M : ℝ) := by
    have h_raw := product_inequality_from_b1
      (hnm := hnm) (data := data) (N₀ := N₀) (K_nat := K_nat)
      (hK_nat_ge_K := hK_nat_ge_K)
      (h_raw_product := h_raw_product)
      (Q := Q) (hQ := hQ)
    have h1 : coarseData.coarseCount = NΔ := by rfl
    have h2 : coarseData.coarseMultiplicity = MΔ := by rfl
    rw [h1, h2, hfine_count, hfine_mult]
    exact h_raw

  -- Step 6: Prove coarseData.coarseGain ≥ coarseGain_raw - loss_parent
  have h_coarse_gain_formula : coarseData.coarseGain = (εA - loss_parent) * α_actual / 2 - loss_coarse := by rfl
  have h_εA_minus_parent_pos : 0 < εA - loss_parent := by linarith
  have hα_base_le_one : α_base ≤ 1 := by
    calc α_base
      ≤ α_actual := hα_base_le_actual
    _ ≤ 1 := hα_actual_le_one
  have h11 : loss_parent * α_base / 2 ≤ loss_parent / 2 := by
    have h11a : loss_parent * α_base ≤ loss_parent := by
      have h : loss_parent * α_base ≤ loss_parent * 1 :=
        mul_le_mul_of_nonneg_left hα_base_le_one h_loss_parent_nonneg
      have h2 : loss_parent * 1 = loss_parent := by ring
      rw [h2] at h
      exact h
    linarith
  have h12 : loss_parent * α_base / 2 + loss_coarse ≤ loss_parent := by
    linarith [h11, hloss_coarse_le_half]
  have h_coarse_gain_lower : coarseData.coarseGain ≥ coarseGain_raw - loss_parent := by
    rw [h_coarse_gain_formula, h_coarseGain_raw_def]
    have h9a : (εA - loss_parent) * α_actual / 2 ≥ (εA - loss_parent) * α_base / 2 := by
      gcongr
      <;> linarith
    have h9b : (εA - loss_parent) * α_base / 2 - loss_coarse ≥ εA * α_base / 2 - loss_parent := by
      have h10 : (εA - loss_parent) * α_base / 2 = εA * α_base / 2 - loss_parent * α_base / 2 := by ring
      rw [h10]
      linarith [h12]
    linarith

  -- Step 7: Construct LossLedger using ACTUAL coarseData.coarseGain
  have h_budget : netGain ≤ coarseData.coarseGain - fineData.localLoss - pkg.lambda - pkg.rho_M - pkg.loss_K := by
    have h_pkg_loss_K : pkg.loss_K = loss_B1 := by rfl
    have h_pkg_lambda : pkg.lambda = lambda := by rfl
    have h_pkg_rho_M : pkg.rho_M = rho_M := by rfl
    rw [h_pkg_lambda, h_pkg_rho_M, h_pkg_loss_K]
    have h5 : coarseData.coarseGain - fineData.localLoss - lambda - rho_M - loss_B1 ≥
        coarseGain_raw - localLoss - lambda - rho_M - loss_B1 - loss_parent := by
      have h6 : coarseData.coarseGain ≥ coarseGain_raw - loss_parent := h_coarse_gain_lower
      have h7 : fineData.localLoss ≤ localLoss := hfine_loss
      linarith
    exact le_trans h_selector_budget h5
  let simpleLedger : DirecretisedFurstenbergEstimate.Section6.LossLedger
      coarseData.coarseGain fineData.localLoss (pkg := pkg) :=
    { netGain := netGain
      hnetGain_pos := h_netGain_pos
      h_budget := h_budget }

  -- Step 8: fineTubes card equality
  have h_card_eq : fineTubes.card = pkg.N₀ := by
    have h1 : pkg.N₀ = N₀ := by rfl
    rw [h1]
    exact h_fineTubes_card

  -- Step 9: Call coarse_branch_combination
  exact coarse_branch_combination
    (hn_pos := hn_pos)
    (hs_pos := hs_pos)
    (hεInc_pos := hεInc_pos)
    (hδ_pos := hδ_pos)
    (coarseData := coarseData)
    (fineData := fineData)
    (pkg := pkg)
    (h_product := h_product)
    (ledger := simpleLedger)
    (fineTubes := fineTubes)
    (h_card_eq := h_card_eq)
    (hm := hm)
    (hb := hb)
    (h_scale := h_scale)
    (h_scale2 := h_scale2)
    (h_thick := h_thick)
    (h_absorb := h_absorb)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
