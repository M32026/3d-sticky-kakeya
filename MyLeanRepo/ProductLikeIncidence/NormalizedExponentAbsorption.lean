module

/-
# Normalized Exponent Absorption (FIXED) — Absorb 2*R_ret into qDiffV4

This version correctly handles the δ-dependent normalization radius.
Instead of assuming a constant bound on `2*R1+1`, it uses the V4 box budget:
`4*R ≤ δ^(-qBox)`, which gives `2*R1+1 = 4*R+3 ≤ 4*δ^(-qBox)`.

## Correct calculation

Given:
- `K_BSG_all ≤ δ^(-qDiffV3)`
- `R_ret = 4 * (2*R1+1) / c_bsg_real`
- `c_bsg_real = δ^(22*q_K) / (16 * 3^22)`
- `2*R1+1 = 4*R+3`
- `4*R ≤ δ^(-qBox)`
- `δ^(-qBox) ≥ 1` (since qBox ≥ 0, δ < 1)

Then:
`2*R1+1 = 4*R+3 ≤ δ^(-qBox)+3 ≤ 4*δ^(-qBox)`

`R_ret ≤ 4 * (4*δ^(-qBox)) / (δ^(22*q_K)/(16*3^22))`
`= 256 * 3^22 * δ^(-(22*q_K + qBox))`

`2*R_ret*K_BSG_all ≤ 512*3^22 * δ^(-(qDiffV3 + 22*q_K + qBox))`

The V4 budget gap:
`qDiffV4 - (qDiffV3 + 22*q_K + qBox)`
`= 102*(qKV4-q_K) + 2*(qKAV4-qKA) + η_work/2 + η_work/20 + qAbsorb`
`≥ qAbsorb`

So `δ^qAbsorb ≤ 1/(512*3^22)` absorbs the constant.

## Whiteprint node
Helper for H5→H6 bridge normalized unified exponent bound.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Real

namespace ProductLikeIncidence.ProductReduction

/-- Generic constant absorption via δ-power gap.

If `gap > 0` and `δ^gap ≤ 1/C`, then `C * δ^(-base) ≤ δ^(-(base + gap))`. -/
lemma constant_absorption_via_gap
    {δ base gap C : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C)
    (hgap_pos : 0 < gap)
    (h_threshold : δ ^ gap ≤ 1 / C) :
    C * δ ^ (-base) ≤ δ ^ (-(base + gap)) := by
  have h1 : δ ^ (-(base + gap)) = δ ^ (-base) * δ ^ (-gap) := by
    have h2 : -(base + gap) = -base + -gap := by ring
    rw [h2]
    exact Real.rpow_add hδ_pos (-base) (-gap)
  rw [h1]
  have h4 : δ ^ (-gap) = (δ ^ gap)⁻¹ := Real.rpow_neg hδ_pos.le gap
  have h3 : C ≤ δ ^ (-gap) := by
    rw [h4]
    have h_pos : 0 < δ ^ gap := by positivity
    have h_C_pos : 0 < C := hC_pos
    have h5 : 1 / (δ ^ gap) ≥ 1 / (1 / C) :=
      one_div_le_one_div_of_le (by positivity) h_threshold
    have h6 : 1 / (δ ^ gap) = (δ ^ gap)⁻¹ := by simp [one_div]
    have h7 : 1 / (1 / C) = C := by
      field_simp [h_C_pos.ne'] <;> ring
    rw [h6, h7] at h5
    exact h5
  have h7 : 0 ≤ δ ^ (-base) := by positivity
  have h8 : C * δ ^ (-base) ≤ δ ^ (-gap) * δ ^ (-base) := by
    exact mul_le_mul_of_nonneg_right h3 h7
  have h9 : δ ^ (-gap) * δ ^ (-base) = δ ^ (-base) * δ ^ (-gap) := by ring
  rw [h9] at h8
  exact h8

/-- Bound `2*R1+1 ≤ 4*δ^(-qBox)` from `4*R ≤ δ^(-qBox)` and `2*R1+1 = 4*R+3`.

Uses `δ^(-qBox) ≥ 1` when `0 ≤ qBox` and `0 < δ < 1`. -/
lemma normalization_radius_bound
    {δ R R1 qBox : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hqBox_nonneg : 0 ≤ qBox)
    (h4R_le : 4 * R ≤ δ ^ (-qBox))
    (hR1_eq : 2 * R1 + 1 = 4 * R + 3) :
    2 * R1 + 1 ≤ 4 * δ ^ (-qBox) := by
  have h1 : δ ^ (-qBox) ≥ 1 := by
    have h2 : δ ^ qBox ≤ 1 := by
      apply Real.rpow_le_one
      <;> linarith
    have h3 : δ ^ (-qBox) = (δ ^ qBox)⁻¹ := Real.rpow_neg hδ_pos.le qBox
    rw [h3]
    have h4 : 0 < δ ^ qBox := by positivity
    have h5 : (δ ^ qBox)⁻¹ ≥ 1 := by
      have h6 : δ ^ qBox ≤ 1 := h2
      have h7 : (δ ^ qBox)⁻¹ ≥ 1⁻¹ := by
        gcongr
      simpa using h7
    exact h5
  have h4 : 2 * R1 + 1 = 4 * R + 3 := hR1_eq
  rw [h4]
  have h5 : 4 * R + 3 ≤ δ ^ (-qBox) + 3 := by linarith [h4R_le]
  have h6 : δ ^ (-qBox) + 3 ≤ 4 * δ ^ (-qBox) := by
    have h7 : 3 ≤ 3 * δ ^ (-qBox) := by
      have h8 : 1 ≤ δ ^ (-qBox) := h1
      nlinarith
    linarith
  linarith

/-- V4 normalized exponent absorption (FIXED): `2 * R_ret * K_BSG_all ≤ δ^(-qDiffV4)`.

Uses the V4 box budget `4*R ≤ δ^(-qBox)` instead of a constant bound on the
normalization radius.
-/
lemma v4_normalized_exponent_absorption
    {δ q_K qKA qAbsorb qDiffV3 qKV4 qKAV4 qGraphV4 qBox qNormChunkV4 qDiffV4 η_work R R1 : ℝ}
    {K_BSG_all R_ret : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    -- Exponent relationships
    (hqDiffV3_eq : qDiffV3 = 80 * q_K + 2 * qKA + qAbsorb)
    (hqKV4_ge : qKV4 ≥ q_K)
    (hqKAV4_ge : qKAV4 ≥ qKA)
    (hGraphV4_eq : qGraphV4 = 22 * qKV4 + η_work / 2 + η_work / 20)
    (hη_work_pos : 0 < η_work)
    (hqBox_nonneg : 0 ≤ qBox)
    (hNormChunk_eq : qNormChunkV4 = qGraphV4 + qBox + qAbsorb)
    (hDiffV4_eq : qDiffV4 = 80 * qKV4 + 2 * qKAV4 + qAbsorb + qNormChunkV4)
    -- Normalization radius bound
    (h4R_le_qbox : 4 * R ≤ δ ^ (-qBox))
    (hR1_eq : 2 * R1 + 1 = 4 * R + 3)
    -- Helper5 outputs
    (hK_BSG_all_le : K_BSG_all ≤ δ ^ (-qDiffV3))
    (hK_BSG_all_pos : 0 < K_BSG_all)
    (hR_ret_eq : R_ret = 4 * (2 * R1 + 1) / (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))))
    -- Absorption threshold
    (h_absorb : δ ^ qAbsorb ≤ 1 / (512 * (3 ^ 22 : ℝ)))
    (hqAbsorb_pos : 0 < qAbsorb) :
    2 * R_ret * K_BSG_all ≤ δ ^ (-qDiffV4) := by
  -- Step 0: Bound 2*R1+1 using box budget
  have hR1_bound : 2 * R1 + 1 ≤ 4 * δ ^ (-qBox) :=
    normalization_radius_bound hδ_pos hδ_lt_one hqBox_nonneg h4R_le_qbox hR1_eq

  -- Step 1: Bound R_ret
  have h1_pos : 0 < δ ^ (22 * q_K) := by positivity
  have hR_ret_bound : R_ret ≤ 256 * (3 ^ 22 : ℝ) * δ ^ (-(22 * q_K + qBox)) := by
    rw [hR_ret_eq]
    have h4 : 4 * (2 * R1 + 1) / (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) =
        4 * (2 * R1 + 1) * (16 * (3 ^ 22 : ℝ)) / δ ^ (22 * q_K) := by
      field_simp [h1_pos.ne']
    rw [h4]
    have h5 : 4 * (2 * R1 + 1) ≤ 16 * δ ^ (-qBox) := by linarith [hR1_bound]
    have h6 : 4 * (2 * R1 + 1) * (16 * (3 ^ 22 : ℝ)) ≤
        256 * (3 ^ 22 : ℝ) * δ ^ (-qBox) := by linarith
    have h7 : δ ^ (-(22 * q_K + qBox)) = δ ^ (-(22 * q_K)) * δ ^ (-qBox) := by
      have h71 : -(22 * q_K + qBox) = -(22 * q_K) + -qBox := by ring
      rw [h71]
      exact Real.rpow_add hδ_pos (-(22 * q_K)) (-qBox)
    have h8 : (4 * (2 * R1 + 1) * (16 * (3 ^ 22 : ℝ))) / δ ^ (22 * q_K) ≤
        256 * (3 ^ 22 : ℝ) * δ ^ (-(22 * q_K + qBox)) := by
      have h9 : (4 * (2 * R1 + 1) * (16 * (3 ^ 22 : ℝ))) / δ ^ (22 * q_K) =
          (4 * (2 * R1 + 1) * (16 * (3 ^ 22 : ℝ))) * (δ ^ (22 * q_K))⁻¹ := by
        field_simp [h1_pos.ne']
      rw [h9]
      have h10 : 0 ≤ (δ ^ (22 * q_K))⁻¹ := by positivity
      have h11 : (4 * (2 * R1 + 1) * (16 * (3 ^ 22 : ℝ))) * (δ ^ (22 * q_K))⁻¹ ≤
          (256 * (3 ^ 22 : ℝ) * δ ^ (-qBox)) * (δ ^ (22 * q_K))⁻¹ :=
        mul_le_mul_of_nonneg_right h6 h10
      have h12 : (256 * (3 ^ 22 : ℝ) * δ ^ (-qBox)) * (δ ^ (22 * q_K))⁻¹ =
          256 * (3 ^ 22 : ℝ) * ((δ ^ (22 * q_K))⁻¹ * δ ^ (-qBox)) := by ring
      rw [h12] at h11
      have h13 : (δ ^ (22 * q_K))⁻¹ * δ ^ (-qBox) = δ ^ (-(22 * q_K + qBox)) := by
        have h14 : (δ ^ (22 * q_K))⁻¹ = δ ^ (-(22 * q_K)) :=
          (Real.rpow_neg hδ_pos.le (22 * q_K)).symm
        rw [h14]
        exact h7.symm
      rw [h13] at h11
      exact h11
    exact h8

  -- Step 2: Bound 2 * R_ret * K_BSG_all
  have h_rpow_add : δ ^ (-(22 * q_K + qBox)) * δ ^ (-qDiffV3) =
      δ ^ (-(qDiffV3 + 22 * q_K + qBox)) := by
    have h13 := Real.rpow_add hδ_pos (-(22 * q_K + qBox)) (-qDiffV3)
    have h14 : -(22 * q_K + qBox) + -qDiffV3 = -(qDiffV3 + 22 * q_K + qBox) := by ring
    rw [h14] at h13
    exact h13.symm
  have h_main : 2 * R_ret * K_BSG_all ≤
      (512 * (3 ^ 22 : ℝ)) * δ ^ (-(qDiffV3 + 22 * q_K + qBox)) := by
    have h8 : 2 * R_ret * K_BSG_all ≤
        2 * (256 * (3 ^ 22 : ℝ) * δ ^ (-(22 * q_K + qBox))) * K_BSG_all := by gcongr
    calc
      2 * R_ret * K_BSG_all
        ≤ 2 * (256 * (3 ^ 22 : ℝ) * δ ^ (-(22 * q_K + qBox))) * K_BSG_all := h8
      _ = (512 * (3 ^ 22 : ℝ)) * (δ ^ (-(22 * q_K + qBox)) * K_BSG_all) := by ring
      _ ≤ (512 * (3 ^ 22 : ℝ)) * (δ ^ (-(22 * q_K + qBox)) * δ ^ (-qDiffV3)) := by gcongr
      _ = (512 * (3 ^ 22 : ℝ)) * δ ^ (-(qDiffV3 + 22 * q_K + qBox)) := by rw [h_rpow_add]

  -- Step 3: Show qDiffV4 - (qDiffV3 + 22*q_K + qBox) ≥ qAbsorb
  have h_gap : qDiffV4 - (qDiffV3 + 22 * q_K + qBox) ≥ qAbsorb := by
    rw [hDiffV4_eq, hqDiffV3_eq, hNormChunk_eq, hGraphV4_eq]
    have h13 : 0 ≤ qKV4 - q_K := by linarith
    have h14 : 0 ≤ qKAV4 - qKA := by linarith
    have h15 : 0 < η_work / 2 + η_work / 20 := by positivity
    nlinarith

  -- Step 4: Set gap and absorb constant
  set gap : ℝ := qDiffV4 - (qDiffV3 + 22 * q_K + qBox) with hgap_def
  have hgap_pos : 0 < gap := by
    have h : gap ≥ qAbsorb := by simpa [hgap_def] using h_gap
    linarith [hqAbsorb_pos]
  have h_eq : qDiffV4 = qDiffV3 + 22 * q_K + qBox + gap := by
    simp [hgap_def]
  have h16 : δ ^ gap ≤ δ ^ qAbsorb := by
    have h17 : qAbsorb ≤ gap := by linarith [h_gap]
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h17
  have h17 : δ ^ gap ≤ 1 / (512 * (3 ^ 22 : ℝ)) :=
    le_trans h16 h_absorb
  have h18 : (512 * (3 ^ 22 : ℝ)) * δ ^ (-(qDiffV3 + 22 * q_K + qBox)) ≤
      δ ^ (-(qDiffV3 + 22 * q_K + qBox + gap)) :=
    constant_absorption_via_gap hδ_pos hδ_lt_one (by positivity) hgap_pos h17
  have h19 : δ ^ (-qDiffV4) = δ ^ (-(qDiffV3 + 22 * q_K + qBox + gap)) := by
    rw [h_eq]
  rw [h19]
  exact le_trans h_main h18

end ProductLikeIncidence.ProductReduction
