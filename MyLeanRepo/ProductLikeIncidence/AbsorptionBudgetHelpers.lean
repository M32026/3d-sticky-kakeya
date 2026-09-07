module

/-
# Absorption Budget Helpers

Helper lemmas for the numeric budget conditions needed by the V4 absorption bridges
in `Helper6AbsorptionBridges.lean`.

## Constant resolution

We choose `C = 256 * 3^32`. This works because:
- Retention: box bound gives `(2*R_norm+3)*δ^qBox ≤ 4`, so `C ≥ 64*3^32*4 = 256*3^32`
- Threshold: KBSG gives `δ^(-qAbsorb) ≥ 81*2^39*3^80 >> 256*3^32`

## Lemmas

1. `box_bound_factor4` — `(2*R_norm+3) * δ^qBox ≤ 4`
2. `retention_ratio_lower` — `c_ret/M_ret ≥ δ^(32*q_K+qBox)/(256*3^32)`
3. `qabsorb_threshold` — `δ^qAbsorb ≤ 1/(256*3^32)`
4. `regularity_threshold` — `δ^εnc ≤ K_work/(2*C_BSG*R_ret)`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4

@[expose] public section

open ProductLikeIncidence.ProductReduction

namespace ProductLikeIncidence.ProductReduction

/-! ## 0. Box bound factor -/

/-- From `2*R_norm ≤ δ^(-qBox)`, derive `(2*R_norm+3) * δ^qBox ≤ 4`. -/
lemma box_bound_factor4
    {δ qBox R_norm : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hqBox_nonneg : 0 ≤ qBox)
    (hR_norm_nonneg : 0 ≤ R_norm)
    (h2R_norm_le : 2 * R_norm ≤ δ ^ (-qBox)) :
    (2 * R_norm + 3) * δ ^ qBox ≤ 4 := by
  have h3 : 2 * R_norm ≤ δ ^ (-qBox) := h2R_norm_le
  have h4 : δ ^ qBox ≤ 1 := Real.rpow_le_one hδ_pos.le hδ_lt_one.le hqBox_nonneg
  have h_posq : 0 < δ ^ qBox := by positivity
  have h7 : δ ^ (-qBox) * δ ^ qBox = 1 := by
    have h71 : δ ^ (-qBox) * δ ^ qBox = δ ^ ((-qBox) + qBox) := by
      rw [← Real.rpow_add hδ_pos]
    have h72 : (-qBox) + qBox = 0 := by ring
    rw [h71, h72]
    simp
  have h8 : (2 * R_norm) * δ ^ qBox ≤ 1 := by
    calc (2 * R_norm) * δ ^ qBox
      ≤ (δ ^ (-qBox)) * δ ^ qBox := by gcongr
    _ = 1 := by rw [h7]
  have h9 : 3 * δ ^ qBox ≤ 3 := by
    have h91 : 0 ≤ (3 : ℝ) := by positivity
    have h92 : 3 * δ ^ qBox ≤ 3 * 1 := mul_le_mul_of_nonneg_left h4 h91
    simpa using h92
  have h10 : (2 * R_norm + 3) * δ ^ qBox = (2 * R_norm) * δ ^ qBox + 3 * δ ^ qBox := by ring
  rw [h10]
  linarith

/-! ## 1. Retention ratio lower bound -/

/-- Retention ratio: `c_ret/M_ret ≥ δ^(32*q_K+qBox)/(256*3^32)`. -/
lemma retention_ratio_lower
    {δ q_K qBox R_norm M_ret c_ret : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hq_K_pos : 0 < q_K) (hqBox_nonneg : 0 ≤ qBox)
    (hR_norm_nonneg : 0 ≤ R_norm)
    (hM_ret_eq : M_ret = (2 * R_norm + 3) * (3 ^ 10 : ℝ) / δ ^ (10 * q_K))
    (hc_ret_eq : c_ret = δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4)
    (h2R_norm_le : 2 * R_norm ≤ δ ^ (-qBox)) :
    c_ret / M_ret ≥ δ ^ (32 * q_K + qBox) / (256 * (3 ^ 32 : ℝ)) := by
  have h_pos10 : 0 < δ ^ (10 * q_K) := by positivity
  have h_posR : 0 < 2 * R_norm + 3 := by linarith
  have h_pow32 : δ ^ (22 * q_K) * δ ^ (10 * q_K) = δ ^ (32 * q_K) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  have h1 : c_ret / M_ret =
      δ ^ (32 * q_K) / ((64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3)) := by
    rw [hc_ret_eq, hM_ret_eq]
    have h_cretd : δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4 =
        δ ^ (22 * q_K) / ((64 : ℝ) * (3 ^ 22 : ℝ)) := by
      field_simp <;> ring
    rw [h_cretd]
    have h_div : (δ ^ (22 * q_K) / ((64 : ℝ) * (3 ^ 22 : ℝ))) /
        (((2 * R_norm + 3) * (3 ^ 10 : ℝ)) / δ ^ (10 * q_K)) =
        (δ ^ (22 * q_K) * δ ^ (10 * q_K)) /
        (((64 : ℝ) * (3 ^ 22 : ℝ)) * ((2 * R_norm + 3) * (3 ^ 10 : ℝ))) := by
      field_simp [h_pos10.ne', h_posR.ne'] <;> ring
    rw [h_div]
    have h_denom : ((64 : ℝ) * (3 ^ 22 : ℝ)) * ((2 * R_norm + 3) * (3 ^ 10 : ℝ)) =
        (64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3) := by ring
    rw [h_denom, h_pow32]
  rw [h1]
  have h_box : (2 * R_norm + 3) * δ ^ qBox ≤ 4 :=
    box_bound_factor4 hδ_pos hδ_lt_one hqBox_nonneg hR_norm_nonneg h2R_norm_le
  have h_pos32 : 0 < δ ^ (32 * q_K) := by positivity
  have h_pos64 : 0 < (64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3) := by positivity
  have h_pos256 : 0 < (256 : ℝ) * (3 ^ 32 : ℝ) := by positivity
  have h9 : (64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3) * δ ^ qBox ≤
      (256 : ℝ) * (3 ^ 32 : ℝ) := by
    have h10 : (64 : ℝ) * (3 ^ 32 : ℝ) * ((2 * R_norm + 3) * δ ^ qBox) ≤
        (64 : ℝ) * (3 ^ 32 : ℝ) * 4 := by gcongr
    have h10' : (64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3) * δ ^ qBox =
        (64 : ℝ) * (3 ^ 32 : ℝ) * ((2 * R_norm + 3) * δ ^ qBox) := by ring
    have h11 : (64 : ℝ) * (3 ^ 32 : ℝ) * 4 = (256 : ℝ) * (3 ^ 32 : ℝ) := by ring
    rw [h10']
    rw [h11] at h10; exact h10
  have h12 : 1 / ((64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3)) ≥
      δ ^ qBox / (256 * (3 ^ 32 : ℝ)) := by
    have h13 : 0 < δ ^ qBox := by positivity
    field_simp [h_pos64.ne', h_pos256.ne', h13.ne'] at h9 ⊢ <;> linarith
  have h14 : δ ^ (32 * q_K) / ((64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3)) =
      δ ^ (32 * q_K) * (1 / ((64 : ℝ) * (3 ^ 32 : ℝ) * (2 * R_norm + 3))) := by
    field_simp [h_pos64.ne'] <;> ring
  have h_pow_add : δ ^ (32 * q_K + qBox) = δ ^ (32 * q_K) * δ ^ qBox := by
    rw [← Real.rpow_add hδ_pos] <;> ring
  rw [h14, h_pow_add]
  have h15 : δ ^ (32 * q_K) * δ ^ qBox / (256 * (3 ^ 32 : ℝ)) =
      δ ^ (32 * q_K) * (δ ^ qBox / (256 * (3 ^ 32 : ℝ))) := by
    field_simp [h_pos256.ne'] <;> ring
  rw [h15]
  gcongr

/-! ## 2. qAbsorb threshold -/

/-- Generic qAbsorb threshold for `C = 256 * 3^32`, taking a plain real exponent. -/
lemma qabsorb_threshold_val
    {δ qAbsorb_val : ℝ} (hδ_pos : 0 < δ)
    (h_KBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-qAbsorb_val)) :
    δ ^ qAbsorb_val ≤ 1 / ((256 : ℝ) * (3 ^ 32 : ℝ)) := by
  have h_pos : 0 < δ ^ qAbsorb_val := by positivity
  have h2 : δ ^ (-qAbsorb_val) = (δ ^ qAbsorb_val)⁻¹ := by
    rw [Real.rpow_neg hδ_pos.le]
  have h3 : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≥ (256 : ℝ) * (3 ^ 32 : ℝ) := by norm_num
  have h4 : (δ ^ qAbsorb_val)⁻¹ ≥ (256 : ℝ) * (3 ^ 32 : ℝ) := by
    rw [h2] at h_KBSG_absorb
    exact le_trans h3 h_KBSG_absorb
  have h5 : 0 < (256 : ℝ) * (3 ^ 32 : ℝ) := by positivity
  have h6 : (δ ^ qAbsorb_val)⁻¹ ≥ (256 : ℝ) * (3 ^ 32 : ℝ) := h4
  have h7 : 1 ≥ (256 : ℝ) * (3 ^ 32 : ℝ) * δ ^ qAbsorb_val := by
    have h8 : (δ ^ qAbsorb_val)⁻¹ = 1 / (δ ^ qAbsorb_val) := by
      field_simp [h_pos.ne']
    rw [h8] at h6
    field_simp [h_pos.ne', h5.ne'] at h6 ⊢ <;> linarith
  have h9 : δ ^ qAbsorb_val ≤ 1 / ((256 : ℝ) * (3 ^ 32 : ℝ)) := by
    have h10 : 0 < (256 : ℝ) * (3 ^ 32 : ℝ) := h5
    calc δ ^ qAbsorb_val
      = ((256 : ℝ) * (3 ^ 32 : ℝ) * δ ^ qAbsorb_val) / ((256 : ℝ) * (3 ^ 32 : ℝ)) := by field_simp [h10.ne'] <;> ring
    _ ≤ 1 / ((256 : ℝ) * (3 ^ 32 : ℝ)) := by gcongr
  exact h9

/-- qAbsorb threshold for `C = 256 * 3^32`. -/
lemma qabsorb_threshold
    {δ η_work : ℝ} (hδ_pos : 0 < δ)
    (h_KBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-(qAbsorb η_work))) :
    δ ^ (qAbsorb η_work) ≤ 1 / ((256 : ℝ) * (3 ^ 32 : ℝ)) :=
  qabsorb_threshold_val hδ_pos h_KBSG_absorb

/-! ## 3. Regularity threshold -/

/-- Regularity threshold: `δ^εnc ≤ K_work / (2*C_BSG*R_ret)`.

Requires `h_budget_ineq : εnc/2 ≥ 32*q_K + 2*qAbsorb + qBox`. -/
lemma regularity_threshold
    {δ εnc q_K qAbsorb qBox R_norm C_A K_ring K_work C_BSG R_ret : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hq_K_pos : 0 < q_K) (hεnc_pos : 0 < εnc)
    (hR_norm_nonneg : 0 ≤ R_norm)
    (hK_ring_pos : 0 < K_ring)
    (hC_A_eq : C_A = K_ring * δ ^ (-εnc / 2))
    (hK_work_eq : K_work = K_ring)
    (hC_BSG_eq : C_BSG = C_A * δ ^ (-(10 * q_K + qAbsorb)))
    (hR_ret_eq : R_ret = (64 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-22 * q_K))
    (h2R_norm_le : 2 * R_norm ≤ δ ^ (-qBox))
    (hqBox_nonneg : 0 ≤ qBox)
    (h_KBSG_absorb : (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 ≤ δ ^ (-qAbsorb))
    (h_budget_ineq : εnc / 2 ≥ 32 * q_K + 2 * qAbsorb + qBox) :
    δ ^ εnc ≤ K_work / (2 * C_BSG * R_ret) := by
  have h_posR : 0 < 2 * R_norm + 3 := by linarith
  have h_posCBSG : 0 < C_BSG := by rw [hC_BSG_eq, hC_A_eq]; positivity
  have h_posRret : 0 < R_ret := by rw [hR_ret_eq]; positivity
  have h_product : 2 * C_BSG * R_ret =
      (128 : ℝ) * (3 ^ 22 : ℝ) * K_ring * (2 * R_norm + 3) *
      δ ^ (-εnc / 2 - 32 * q_K - qAbsorb) := by
    rw [hC_BSG_eq, hR_ret_eq, hC_A_eq]
    have h_pow : δ ^ (-εnc / 2) * δ ^ (-(10 * q_K + qAbsorb)) * δ ^ (-22 * q_K) =
        δ ^ (-εnc / 2 - 32 * q_K - qAbsorb) := by
      rw [← Real.rpow_add hδ_pos, ← Real.rpow_add hδ_pos] <;> ring_nf
    have h_goal : 2 * (K_ring * δ ^ (-εnc / 2) * δ ^ (-(10 * q_K + qAbsorb))) *
        ((64 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-22 * q_K)) =
        (128 : ℝ) * (3 ^ 22 : ℝ) * K_ring * (2 * R_norm + 3) *
        (δ ^ (-εnc / 2) * δ ^ (-(10 * q_K + qAbsorb)) * δ ^ (-22 * q_K)) := by ring
    rw [h_goal, h_pow] <;> ring
  rw [h_product, hK_work_eq]
  have h_box4 : (2 * R_norm + 3) * δ ^ qBox ≤ 4 :=
    box_bound_factor4 hδ_pos hδ_lt_one hqBox_nonneg hR_norm_nonneg h2R_norm_le
  have h1 : (2 * R_norm + 3) ≤ 4 * δ ^ (-qBox) := by
    have h_posq : 0 < δ ^ qBox := by positivity
    have h2 : (2 * R_norm + 3) * δ ^ qBox ≤ 4 := h_box4
    have h4 : δ ^ qBox * δ ^ (-qBox) = 1 := by
      have h5 : qBox + (-qBox) = 0 := by ring
      have h6 : δ ^ qBox * δ ^ (-qBox) = δ ^ (qBox + (-qBox)) := by
        rw [← Real.rpow_add hδ_pos]
      rw [h6, h5]
      simp
    have h3 : ((2 * R_norm + 3) * δ ^ qBox) * δ ^ (-qBox) = (2 * R_norm + 3) := by
      have h5 : ((2 * R_norm + 3) * δ ^ qBox) * δ ^ (-qBox) =
          (2 * R_norm + 3) * (δ ^ qBox * δ ^ (-qBox)) := by ring
      rw [h5, h4] <;> ring
    have h7 : ((2 * R_norm + 3) * δ ^ qBox) * δ ^ (-qBox) ≤ 4 * δ ^ (-qBox) := by
      gcongr
    rw [h3] at h7
    exact h7
  have h_ineq : εnc / 2 - 32 * q_K - qAbsorb - qBox ≥ qAbsorb := by linarith
  have h6 : δ ^ (εnc / 2 - 32 * q_K - qAbsorb - qBox) ≤ δ ^ qAbsorb :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_ineq
  have h7 : δ ^ qAbsorb ≤ 1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80) := by
    set K : ℝ := (81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80 with hK
    have hK_pos : 0 < K := by positivity
    have h_pos : 0 < δ ^ qAbsorb := by positivity
    have h2 : δ ^ (-qAbsorb) = (δ ^ qAbsorb)⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le]
    have h3 : (δ ^ qAbsorb)⁻¹ ≥ K := by
      rw [h2] at h_KBSG_absorb
      exact h_KBSG_absorb
    have h4 : K * δ ^ qAbsorb ≤ 1 := by
      have h5 : (δ ^ qAbsorb)⁻¹ ≥ K := h3
      have h6 : (δ ^ qAbsorb)⁻¹ = 1 / (δ ^ qAbsorb) := by
        field_simp [h_pos.ne']
      rw [h6] at h5
      have h7 : 1 / (δ ^ qAbsorb) ≥ K := h5
      have h8 : K * δ ^ qAbsorb ≤ 1 := by
        calc K * δ ^ qAbsorb
          ≤ (1 / (δ ^ qAbsorb)) * δ ^ qAbsorb := by gcongr
        _ = 1 := by
          field_simp [h_pos.ne'] <;> ring
      exact h8
    have h9 : δ ^ qAbsorb ≤ 1 / K := by
      calc δ ^ qAbsorb
        = (K * δ ^ qAbsorb) / K := by field_simp [hK_pos.ne'] <;> ring
      _ ≤ 1 / K := by gcongr
    exact h9
  have h8 : (1 / ((81 : ℝ) * (2 : ℝ)^39 * (3 : ℝ)^80)) ≤
      1 / ((512 : ℝ) * (3 ^ 22 : ℝ)) := by
    gcongr <;> norm_num
  have h9 : δ ^ (εnc / 2 - 32 * q_K - qAbsorb - qBox) ≤
      1 / ((512 : ℝ) * (3 ^ 22 : ℝ)) :=
    le_trans h6 (le_trans h7 h8)
  have h10 : 0 < δ ^ (εnc / 2 - 32 * q_K - qAbsorb - qBox) := by positivity
  have h11 : (512 : ℝ) * (3 ^ 22 : ℝ) ≤
      δ ^ (-εnc / 2 + 32 * q_K + qAbsorb + qBox) := by
    have h12 : -εnc / 2 + 32 * q_K + qAbsorb + qBox =
        -(εnc / 2 - 32 * q_K - qAbsorb - qBox) := by ring
    rw [h12]
    have h13 : δ ^ (-(εnc / 2 - 32 * q_K - qAbsorb - qBox)) =
        (δ ^ (εnc / 2 - 32 * q_K - qAbsorb - qBox))⁻¹ := by
      rw [Real.rpow_neg hδ_pos.le] <;> ring
    rw [h13]
    have h14 : 0 < (512 : ℝ) * (3 ^ 22 : ℝ) := by positivity
    field_simp [h10.ne'] at h9 ⊢ <;> linarith
  have h_main : (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) ≤
      δ ^ (-εnc / 2 + 32 * q_K + qAbsorb) := by
    calc (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3)
      ≤ (128 : ℝ) * (3 ^ 22 : ℝ) * (4 * δ ^ (-qBox)) := by gcongr
    _ = (512 : ℝ) * (3 ^ 22 : ℝ) * δ ^ (-qBox) := by ring
    _ ≤ δ ^ (-εnc / 2 + 32 * q_K + qAbsorb + qBox) * δ ^ (-qBox) := by gcongr
    _ = δ ^ (-εnc / 2 + 32 * q_K + qAbsorb) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
  set e1 : ℝ := -εnc / 2 + 32 * q_K + qAbsorb with he1
  set e2 : ℝ := εnc / 2 - 32 * q_K - qAbsorb with he2
  have h_e_sum : e1 + e2 = 0 := by
    simp only [he1, he2] <;> ring
  have h_pow_prod : δ ^ e1 * δ ^ e2 = 1 := by
    have h : δ ^ e1 * δ ^ e2 = δ ^ (e1 + e2) := by
      rw [← Real.rpow_add hδ_pos]
    rw [h, h_e_sum]
    simp
  have h_pos_e2 : 0 < δ ^ e2 := by positivity
  have h_goal1 : (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ e2 ≤ 1 := by
    calc (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ e2
      ≤ δ ^ e1 * δ ^ e2 := by gcongr
    _ = 1 := h_pow_prod
  have h_posD : 0 < (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ e2 := by positivity
  have h2 : δ ^ εnc ≤ 1 / ((128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) := by
    have h_eq_e2 : εnc + (-εnc / 2 - 32 * q_K - qAbsorb) = e2 := by
      simp only [he2] <;> ring
    have h_pow3 : δ ^ εnc * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb) = δ ^ e2 := by
      rw [← Real.rpow_add hδ_pos, h_eq_e2]
    have h4 : δ ^ εnc * ((128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) ≤ 1 := by
      have h5 : δ ^ εnc * ((128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) =
          (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * (δ ^ εnc * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) := by ring
      rw [h5, h_pow3]
      exact h_goal1
    have h_posD' : 0 < (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb) := by positivity
    have h_iff : δ ^ εnc ≤ 1 / ((128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) ↔
        δ ^ εnc * ((128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) ≤ 1 := by
      exact le_div_iff₀ h_posD'
    exact h_iff.mpr h4
  have h3 : K_ring / ((128 : ℝ) * (3 ^ 22 : ℝ) * K_ring * (2 * R_norm + 3) *
      δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) =
      1 / ((128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) *
      δ ^ (-εnc / 2 - 32 * q_K - qAbsorb)) := by
    have h_posK : 0 < K_ring := hK_ring_pos
    have h_posD' : 0 < (128 : ℝ) * (3 ^ 22 : ℝ) * (2 * R_norm + 3) * δ ^ (-εnc / 2 - 32 * q_K - qAbsorb) := by positivity
    field_simp [h_posK.ne', h_posD'.ne'] <;> ring
  rw [h3]
  exact h2

end ProductLikeIncidence.ProductReduction
