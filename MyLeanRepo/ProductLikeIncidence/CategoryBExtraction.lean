module

/-
# Category B Fixes — Energy Absorption and Extraction Constant

Two lemmas for the endgame energy pipeline:

1. `energy_absorption_bound`: proves `L^(2κ) * (δ/L)^(-q_coord) ≤ (δ/L)^(-q_norm)`
   from the WireBudgetsV3 exponent definitions and the Phase0 box bound.

2. `extraction_constant_bound`: proves `energyToLargeMassDeltaSetC (δ/L) κ0 K' ≤ K_ring * δ^{-εnc}`
   using the log-square absorption lemma and the budget gap.

The key exponent choice: `α = εnc/(1+qBox) - q_norm > 0` (from the gap),
so `(1+qBox)*(q_norm+α) = εnc` exactly.

## Whiteprint node
Helper for `incidence_to_ring_contradiction`.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.Energy.EnergyToLargeMassDeltaSet
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open ProductLikeIncidence.ProductReduction

namespace ProductLikeIncidence.ProductReduction

/-- Helper: if `0 < x ≤ y` and `c > 0`, then `y^(-c) ≤ x^(-c)`. -/
private lemma rpow_neg_le_of_le {x y c : ℝ} (hx_pos : 0 < x) (hxy : x ≤ y)
    (hc_pos : 0 < c) : y ^ (-c) ≤ x ^ (-c) := by
  have h1 : x ^ c ≤ y ^ c := Real.rpow_le_rpow hx_pos.le hxy hc_pos.le
  have h2 : 0 < x ^ c := Real.rpow_pos_of_pos hx_pos c
  have h3 : 1 / (y ^ c) ≤ 1 / (x ^ c) := one_div_le_one_div_of_le h2 h1
  have h4 : y ^ (-c) = 1 / (y ^ c) := by
    rw [Real.rpow_neg (by linarith)] <;> field_simp
  have h5 : x ^ (-c) = 1 / (x ^ c) := by
    rw [Real.rpow_neg (by linarith)] <;> field_simp
  rw [h4, h5]
  exact h3

/-- **Energy absorption bound** (Category B).

    Given `L ≤ δ^{-qBox}`, prove:
    `L^(2κ) * (δ/L)^(-q_coord_energy) ≤ (δ/L)^(-q_norm_energy)`.

    Key identity: `q_norm_energy = q_coord_energy + qEnergy` and
    `qEnergy = 2κ * qBox`, so `L^(2κ) ≤ δ^{-qEnergy} ≤ (δ/L)^{-qEnergy}`. -/
lemma energy_absorption_bound
    {δ L η τ κ : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hL_ge1 : 1 ≤ L)
    (hL_le_qbox : L ≤ δ ^ (-qBox η τ))
    (hη_pos : 0 < η) (hτ_pos : 0 < τ) (hκ_pos : 0 < κ)
    (q_coord_energy q_norm_energy : ℝ)
    (hq_norm_eq : q_norm_energy = q_coord_energy + qEnergy η τ κ) :
    L ^ (2 * κ) * (δ / L) ^ (-q_coord_energy) ≤ (δ / L) ^ (-q_norm_energy) := by
  have hqEnergy_eq : qEnergy η τ κ = 2 * κ * qBox η τ := by
    dsimp only [qEnergy, qBox, qAbsorb] <;> ring
  have hqBox_pos : 0 < qBox η τ := by
    dsimp only [qBox, qAbsorb]
    have h1 : 0 < η := hη_pos
    have h2 : 0 < τ := hτ_pos
    positivity
  have hqEnergy_pos : 0 < qEnergy η τ κ := by
    rw [hqEnergy_eq] <;> positivity
  -- Step 1: L^(2κ) ≤ δ^{-qEnergy}
  have h1 : L ^ (2 * κ) ≤ δ ^ (-qEnergy η τ κ) := by
    have h2 : L ^ (2 * κ) ≤ (δ ^ (-qBox η τ)) ^ (2 * κ) := by
      gcongr <;> linarith
    have h3 : (δ ^ (-qBox η τ)) ^ (2 * κ) = δ ^ ((-qBox η τ) * (2 * κ)) := by
      exact (Real.rpow_mul hδ_pos.le (-qBox η τ) (2 * κ)).symm
    have h4 : (-qBox η τ) * (2 * κ) = -(2 * κ * qBox η τ) := by ring
    rw [h3, h4] at h2
    have h5 : δ ^ (-(2 * κ * qBox η τ)) = δ ^ (-qEnergy η τ κ) := by
      rw [hqEnergy_eq] <;> ring
    rw [h5] at h2
    exact h2
  -- Step 2: δ^{-qEnergy} ≤ (δ/L)^{-qEnergy}
  have hδL_pos : 0 < δ / L := by positivity
  have hδL_leδ : δ / L ≤ δ := by
    have h7 : 1 ≤ L := hL_ge1
    have h8 : δ / L ≤ δ / 1 := by gcongr
    simpa using h8
  have h4 : δ ^ (-qEnergy η τ κ) ≤ (δ / L) ^ (-qEnergy η τ κ) :=
    rpow_neg_le_of_le hδL_pos hδL_leδ hqEnergy_pos
  have h9 : L ^ (2 * κ) ≤ (δ / L) ^ (-qEnergy η τ κ) := le_trans h1 h4
  -- Step 3: Multiply by (δ/L)^{-q_coord_energy}
  have h10 : 0 < (δ / L) ^ (-q_coord_energy) := by positivity
  have h11 : L ^ (2 * κ) * (δ / L) ^ (-q_coord_energy) ≤
      (δ / L) ^ (-qEnergy η τ κ) * (δ / L) ^ (-q_coord_energy) := by gcongr
  have h12 : (δ / L) ^ (-qEnergy η τ κ) * (δ / L) ^ (-q_coord_energy) =
      (δ / L) ^ (-q_norm_energy) := by
    rw [← Real.rpow_add (by positivity)]
    rw [hq_norm_eq] <;> ring_nf
  rw [h12] at h11
  exact h11

/-- Helper: bound `M^2` where `M = ceil(logb_2(δ'^{-(κ+1)})) + 1`.
    For `0 < δ' ≤ 1/4`, `M^2 ≤ C * log^2(1/δ')` with explicit `C`. -/
private lemma extraction_M2_bound {δ' κ : ℝ} (hδ'_pos : 0 < δ') (hδ'_le_quarter : δ' ≤ 1 / 4)
    (hκ_pos : 0 < κ) (hκ_le_one : κ ≤ 1) :
    ((Nat.ceil (Real.logb 2 (δ' ^ (-(κ + 1)))) : ℝ) + 1) ^ 2 ≤
    4 * ((κ + 1) / Real.log 2 + 1) ^ 2 * (Real.log (1 / δ')) ^ 2 := by
  set x : ℝ := Real.logb 2 (δ' ^ (-(κ + 1))) with hx_def
  set M : ℝ := ((Nat.ceil x) : ℝ) + 1 with hM_def
  set L : ℝ := Real.log (1 / δ') with hL_def
  set A : ℝ := (κ + 1) / Real.log 2 with hA_def
  have hL_pos : 0 < L := by
    simp only [hL_def]
    apply Real.log_pos
    have h : 1 / δ' > 1 := by
      have h' : δ' < 1 := by linarith
      field_simp [hδ'_pos.ne'] <;> linarith
    exact h
  have h_logb_eq : x = A * L := by
    simp only [hx_def, hA_def, hL_def]
    have h1 : δ' ^ (-(κ + 1)) = (1 / δ') ^ (κ + 1) := by
      have h11 : δ' ^ (-(κ + 1)) = (δ' ^ (κ + 1))⁻¹ := Real.rpow_neg hδ'_pos.le (κ + 1)
      rw [h11]
      have h12 : (δ' ^ (κ + 1))⁻¹ = (1 / δ') ^ (κ + 1) := by
        have h13 : (1 / δ') ^ (κ + 1) = (1 : ℝ) ^ (κ + 1) / (δ' ^ (κ + 1)) := by
          rw [Real.div_rpow (by positivity) (by positivity)]
        rw [h13] <;> simp [hδ'_pos.ne'] <;> ring
      exact h12
    rw [h1]
    have h2 : Real.logb 2 ((1 / δ') ^ (κ + 1)) =
        Real.log ((1 / δ') ^ (κ + 1)) / Real.log 2 := by rfl
    rw [h2]
    have h3 : Real.log ((1 / δ') ^ (κ + 1)) = (κ + 1) * Real.log (1 / δ') := by
      rw [Real.log_rpow (by positivity)] <;> ring
    rw [h3] <;> ring
  have h_logb_pos : 0 < x := by
    rw [h_logb_eq]
    have hA_pos : 0 < A := by simp only [hA_def] <;> positivity
    exact mul_pos hA_pos hL_pos
  have h_ceil_le : ∀ (y : ℝ), 0 < y → (Nat.ceil y : ℝ) ≤ y + 1 := by
    intro y hy
    set n : ℕ := Nat.ceil y with hn_def
    have hn_pos : 0 < n := Nat.ceil_pos.mpr hy
    have h1 : ¬(y ≤ ↑(n - 1)) := by
      intro h
      have h2 : n ≤ n - 1 := Nat.ceil_le.mpr h
      omega
    have h3 : (↑(n - 1) : ℝ) < y := by exact Std.not_le.mp h1
    have h4 : (n : ℝ) - 1 < y := by
      have h5 : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
        simp [hn_pos, Nat.cast_sub (show n ≥ 1 from hn_pos)] <;> omega
      rw [h5] at h3
      exact h3
    linarith
  have hL_ge_one : 1 ≤ L := by
    simp only [hL_def]
    have h1 : 1 / δ' ≥ 4 := by
      have h2 : δ' ≤ 1 / 4 := hδ'_le_quarter
      have h3 : 0 < δ' := hδ'_pos
      field_simp [h3.ne'] <;> linarith
    have h4 : Real.log (1 / δ') ≥ Real.log 4 := Real.log_le_log (by linarith) (by linarith)
    have h5 : Real.log 4 > 1 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by
        have h7 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
        linarith
      have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      have h9 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      rw [h8] at h9
      exact h9
    linarith
  have hA_nonneg : 0 ≤ A := by simp only [hA_def] <;> positivity
  have hM_le : M ≤ A * L + 2 := by
    have h3 : (Nat.ceil x : ℝ) ≤ x + 1 := h_ceil_le x h_logb_pos
    have h41 : x + 1 = A * L + 1 := by rw [h_logb_eq]
    have h4 : (Nat.ceil x : ℝ) ≤ A * L + 1 := h3.trans_eq h41
    have h5 : M = (Nat.ceil x : ℝ) + 1 := hM_def
    rw [h5]
    linarith
  have hM_le2 : M ≤ (A + 2) * L := by
    calc M
      ≤ A * L + 2 := hM_le
    _ = A * L + 2 * 1 := by ring
    _ ≤ A * L + 2 * L := by gcongr <;> linarith [hL_ge_one]
    _ = (A + 2) * L := by ring
  have h_ineq : (A + 2) ^ 2 ≤ 4 * (A + 1) ^ 2 := by nlinarith [hA_nonneg]
  have hM2_log : M ^ 2 ≤ 4 * (A + 1) ^ 2 * L ^ 2 := by
    have h6 : M ^ 2 ≤ ((A + 2) * L) ^ 2 := by gcongr
    have h7 : ((A + 2) * L) ^ 2 = (A + 2) ^ 2 * L ^ 2 := by ring
    rw [h7] at h6
    have h8 : (A + 2) ^ 2 * L ^ 2 ≤ 4 * (A + 1) ^ 2 * L ^ 2 := by gcongr <;> linarith
    exact le_trans h6 h8
  simpa [hA_def, hL_def] using hM2_log

/-- **Extraction constant bound** (Category B).

    Given the budget gap `(1 + qBox) * q_norm_energy < εnc`, prove for
    sufficiently small `δ`:
    `energyToLargeMassDeltaSetC (δ/L) κ0 (3^(2κ0) * (δ/L)^(-q_norm_energy)) ≤ K_ring * δ^{-εnc}`.

    Exponent choice: `α = εnc/(1+qBox) - q_norm > 0`, so
    `(1+qBox)*(q_norm+α) = εnc` exactly. -/
lemma extraction_constant_bound
    {δ L κ0 εnc K_ring q_norm_energy qBox : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hL_ge1 : 1 ≤ L)
    (hL_le_qbox : L ≤ δ ^ (-qBox))
    (hκ_pos : 0 < κ0) (hκ_le_one : κ0 ≤ 1)
    (hεnc_pos : 0 < εnc)
    (hK_ring_pos : 0 < K_ring)
    (hK_ring_ge_one : 1 ≤ K_ring)
    (hq_norm_pos : 0 < q_norm_energy)
    (hqBox_nonneg : 0 ≤ qBox)
    (h_gap : (1 + qBox) * q_norm_energy < εnc)
    (hδ'_le_quarter : δ / L ≤ 1 / 4)
    (hδ_small : 64 * (10 * (3 : ℝ) ^ (2 * κ0) * (2 : ℝ) ^ κ0) *
        (4 * ((κ0 + 1) / Real.log 2 + 1) ^ 2) * (Real.log (1 / (δ / L))) ^ 2 ≤
      (δ / L) ^ (-(εnc / (1 + qBox) - q_norm_energy))) :
    robust_projection_main.energyToLargeMassDeltaSetC (δ / L) κ0
      ((3 : ℝ) ^ (2 * κ0) * (δ / L) ^ (-q_norm_energy)) ≤ K_ring * δ ^ (-εnc) := by
  set δ' : ℝ := δ / L with hδ'_def
  have hδ'_pos : 0 < δ' := by positivity
  have hδ'_lt_one : δ' < 1 := by
    have h1 : δ' ≤ δ := by
      dsimp only [δ']
      have h2 : 1 ≤ L := hL_ge1
      have h3 : δ / L ≤ δ / 1 := by gcongr
      simpa using h3
    linarith
  set K' : ℝ := (3 : ℝ) ^ (2 * κ0) * δ' ^ (-q_norm_energy) with hK'_def
  set α : ℝ := εnc / (1 + qBox) - q_norm_energy with hα_def
  have h1_pos : 0 < 1 + qBox := by linarith
  have hα_pos : 0 < α := by
    have h2 : (1 + qBox) * q_norm_energy < εnc := h_gap
    have h_eq : q_norm_energy = ((1 + qBox) * q_norm_energy) / (1 + qBox) := by
      field_simp [h1_pos.ne'] <;> ring
    have h3 : q_norm_energy < εnc / (1 + qBox) := by
      rw [h_eq]
      gcongr
    linarith [hα_def]
  have h_exp_eq : (1 + qBox) * (q_norm_energy + α) = εnc := by
    simp only [hα_def] <;> field_simp [h1_pos.ne'] <;> ring
  -- M^2 bound
  set C_log : ℝ := 4 * ((κ0 + 1) / Real.log 2 + 1) ^ 2 with hC_log_def
  set M : ℝ := (Nat.ceil (Real.logb 2 (δ' ^ (-(κ0 + 1)))) + 1 : ℝ) with hM_def
  have hM2_log : M ^ 2 ≤ C_log * (Real.log (1 / δ')) ^ 2 :=
    extraction_M2_bound hδ'_pos hδ'_le_quarter hκ_pos hκ_le_one
  -- Main calculation
  set C_total : ℝ := 64 * (10 * (3 : ℝ) ^ (2 * κ0) * (2 : ℝ) ^ κ0) * C_log with hC_total_def
  have h_main_eq : robust_projection_main.energyToLargeMassDeltaSetC δ' κ0 K' =
      64 * (10 * K' * (2 : ℝ) ^ κ0) * M ^ 2 := by rfl
  rw [h_main_eq]
  have h_bound1 : 64 * (10 * K' * (2 : ℝ) ^ κ0) * M ^ 2 ≤
      C_total * (Real.log (1 / δ')) ^ 2 * δ' ^ (-q_norm_energy) := by
    calc
      64 * (10 * K' * (2 : ℝ) ^ κ0) * M ^ 2
        = 64 * (10 * ((3 : ℝ) ^ (2 * κ0) * δ' ^ (-q_norm_energy)) * (2 : ℝ) ^ κ0) * M ^ 2 := by
          rw [hK'_def]
      _ = 64 * (10 * (3 : ℝ) ^ (2 * κ0) * (2 : ℝ) ^ κ0) * δ' ^ (-q_norm_energy) * M ^ 2 := by ring
      _ ≤ 64 * (10 * (3 : ℝ) ^ (2 * κ0) * (2 : ℝ) ^ κ0) * δ' ^ (-q_norm_energy) *
            (C_log * (Real.log (1 / δ')) ^ 2) := by gcongr <;> exact hM2_log
      _ = C_total * (Real.log (1 / δ')) ^ 2 * δ' ^ (-q_norm_energy) := by
          simp only [hC_total_def] <;> ring
  -- Absorb log^2 into δ'^{-α}
  have h_log_absorb : C_total * (Real.log (1 / δ')) ^ 2 ≤ δ' ^ (-α) := by
    simpa [hC_total_def, hC_log_def, hα_def, hδ'_def] using hδ_small
  have h_combined : C_total * (Real.log (1 / δ')) ^ 2 * δ' ^ (-q_norm_energy) ≤
      δ' ^ (-(q_norm_energy + α)) := by
    calc
      C_total * (Real.log (1 / δ')) ^ 2 * δ' ^ (-q_norm_energy)
        ≤ δ' ^ (-α) * δ' ^ (-q_norm_energy) := by gcongr
      _ = δ' ^ (-(q_norm_energy + α)) := by
        rw [← Real.rpow_add hδ'_pos] <;> ring_nf
  -- Convert δ' to δ: δ' ≥ δ^{1+qBox}
  have hδ'_lower : δ' ≥ δ ^ (1 + qBox) := by
    dsimp only [δ']
    have h2 : L ≤ δ ^ (-qBox) := hL_le_qbox
    have h3 : δ / L ≥ δ / (δ ^ (-qBox)) := by gcongr
    have h4 : δ / (δ ^ (-qBox)) = δ ^ (1 + qBox) := by
      have h5 : δ / (δ ^ (-qBox)) = δ * (δ ^ (-qBox))⁻¹ := by ring
      rw [h5]
      have h6 : (δ ^ (-qBox))⁻¹ = δ ^ qBox := by
        have h61 : δ ^ (-qBox) = (δ ^ qBox)⁻¹ := Real.rpow_neg hδ_pos.le qBox
        rw [h61]
        field_simp [hδ_pos.ne'] <;> ring
      rw [h6]
      have h7 : δ * δ ^ qBox = δ ^ (1 + qBox) := by
        have h71 : δ ^ ((1 : ℝ) + qBox) = δ ^ (1 : ℝ) * δ ^ qBox := Real.rpow_add hδ_pos (1 : ℝ) qBox
        have h72 : δ ^ (1 : ℝ) = δ := by simp
        rw [h72] at h71
        exact h71.symm
      exact h7
    linarith
  have hδ'_pow : δ' ^ (-(q_norm_energy + α)) ≤ δ ^ (-((1 + qBox) * (q_norm_energy + α))) := by
    have h8 : 0 < q_norm_energy + α := by linarith
    have h9 : 0 < δ ^ (1 + qBox) := by positivity
    have h10 : δ ^ (1 + qBox) ≤ δ' := hδ'_lower
    have h11 := rpow_neg_le_of_le h9 h10 h8
    have h12 : (δ ^ (1 + qBox)) ^ (-(q_norm_energy + α)) =
        δ ^ (-((1 + qBox) * (q_norm_energy + α))) := by
      have h13 : (δ ^ (1 + qBox)) ^ (-(q_norm_energy + α)) =
          δ ^ ((1 + qBox) * (-(q_norm_energy + α))) := by
        exact (Real.rpow_mul hδ_pos.le (1 + qBox) (-(q_norm_energy + α))).symm
      rw [h13]
      have h14 : (1 + qBox) * (-(q_norm_energy + α)) = -((1 + qBox) * (q_norm_energy + α)) := by ring
      rw [h14]
    rw [h12] at h11
    exact h11
  have h9 : (1 + qBox) * (q_norm_energy + α) = εnc := h_exp_eq
  have hδ_pow : δ ^ (-((1 + qBox) * (q_norm_energy + α))) = δ ^ (-εnc) := by
    have h10 : -((1 + qBox) * (q_norm_energy + α)) = -εnc := by rw [h9]
    rw [h10]
  have h_final : δ' ^ (-(q_norm_energy + α)) ≤ δ ^ (-εnc) := by
    calc δ' ^ (-(q_norm_energy + α))
      ≤ δ ^ (-((1 + qBox) * (q_norm_energy + α))) := hδ'_pow
    _ = δ ^ (-εnc) := hδ_pow
  have h10 : δ' ^ (-(q_norm_energy + α)) ≤ K_ring * δ ^ (-εnc) := by
    calc δ' ^ (-(q_norm_energy + α))
      ≤ δ ^ (-εnc) := h_final
    _ ≤ K_ring * δ ^ (-εnc) := by
      have h11 : (1 : ℝ) ≤ K_ring := hK_ring_ge_one
      have h12 : 0 ≤ δ ^ (-εnc) := by positivity
      nlinarith
  exact le_trans h_bound1 (le_trans h_combined h10)

end ProductLikeIncidence.ProductReduction
