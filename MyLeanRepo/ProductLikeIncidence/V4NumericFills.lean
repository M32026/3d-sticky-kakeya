module

/-
# V4 Numeric Fills — Production

Standalone numeric lemmas and constants for the V4 endgame skeleton.

Promoted from scratch (aurora/V4NumericFills, fjord/ExtractionGapBridge,
nimbus/SkeletonSorryFills) to production so the skeleton can import them.

## Contents
1. C_sum constant: `C_sumV4`, `C_sumV4_pos`, `C_sum_le_delta_neg_qKV4`
2. c_dense: `cDenseExponentV4`, `c_dense_realV4`, `hc_dense_ge_V4`
3. Constant weakening: `weaken_const_by_delta`
4. KBSG absorption: `absorb_KBSG_V4`
5. BSG terminal regularity: `terminalAbsorptionV4`, `sizeLossCoefficientV4`,
   `terminal_regularity_bound_V4`
6. Size loss: `qSizeLossV4_le_εnc_V4`
7. Extraction gap: `qNormEnergyV3_le_qTotalV4`, `extraction_gap_bridge_enc2`

## Whiteprint node
Numeric fills for `incidence_to_ring_contradiction` V4 budget correction.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical Real

namespace ProductLikeIncidence.ProductReduction

/-! ## 3. Constant weakening via δ-smallness -/

/-- Weaken a constant by a δ-power: given `C > 0`, `e > 0`, and `δ^e ≤ 1/C`,
proves `C ≤ δ^{-e}`. This allows absorbing fixed constants into the budget. -/
lemma weaken_const_by_delta
    {δ C e : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hC_pos : 0 < C) (he_pos : 0 < e)
    (h_small : δ ^ e ≤ 1 / C) :
    C ≤ δ ^ (-e) := by
  have h1 : δ ^ (-e) = (δ ^ e)⁻¹ := by
    rw [Real.rpow_neg (by linarith)] <;> ring
  rw [h1]
  have h2 : C * δ ^ e ≤ 1 := by
    calc C * δ ^ e
      ≤ C * (1 / C) := by gcongr
    _ = 1 := by field_simp [hC_pos.ne'] <;> ring
  have h3 : 0 < δ ^ e := by positivity
  calc C
    = (C * δ ^ e) / (δ ^ e) := by field_simp [h3.ne'] <;> ring
  _ ≤ 1 / (δ ^ e) := by gcongr
  _ = (δ ^ e)⁻¹ := by ring

/-! ## 7. Extraction gap bridge -/

/-- `qNormEnergyV3` is one summand in `qTotalV4`, and all other summands are
nonnegative under standard parameter assumptions, so `qNormEnergyV3 ≤ qTotalV4`. -/
lemma qNormEnergyV3_le_qTotalV4
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hL_nonneg : 0 ≤ L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (_hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep) :
    qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep ≤
      qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  dsimp only [qTotalV4]
  have h_init : 0 ≤ qInitV3 η_work rho_sel := by
    dsimp only [qInitV3, qAbsorb]; linarith
  have h_rho_sep : 0 ≤ 2 * rho_sep := by positivity
  have h_graph : 0 ≤ qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
    dsimp only [qGraphV4, qKV4, qDensityV4, qK, qProjective, qG, qAbsorb]; positivity
  have h_absorb : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
  have hKA_nonneg : 0 ≤ qKAV4 L_exp η_work rho_sel rho_sep := by
    dsimp only [qKAV4, alphaProjectionV4, qMassV4, qAbsorb]
    have h1 : 0 ≤ (L_exp / 2) * η_work := by positivity
    have h2 : 0 ≤ 2 * rho_sep + η_work / 100 := by positivity
    have h3 : 0 ≤ (3 * rho_sel) / 2 := by positivity
    have h4 : 0 ≤ 2 * (η_work / 100) := by positivity
    linarith
  have h_diff : 0 ≤ 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    have h5 : 0 ≤ qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
      dsimp only [qKV4, qDensityV4, qK, qProjective, qAbsorb]
      have h51 : 0 ≤ (L_exp + 2) * η_work := by positivity
      have h52 : 0 ≤ p_projective * ε / κ0 := by positivity
      have h53 : 0 ≤ 3 * rho_sel := by linarith
      have h54 : 0 ≤ 2 * rho_sep := by linarith
      have h55 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
      linarith
    have h6 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    have h7 : 0 ≤ qKAV4 L_exp η_work rho_sel rho_sep := hKA_nonneg
    have h8 : 0 ≤ qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
      dsimp only [qNormChunkV4, qGraphV4, qKV4, qDensityV4, qK, qProjective, qBox, qAbsorb]
      positivity
    dsimp only [qDiffV4]
    positivity
  have h_size : 0 ≤ qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    dsimp only [qSizeLossV4, qEffV4, qNormChunkV4, qGraphV4, qKV4, qDensityV4, qK, qProjective, qG, qAbsorb,
      qInputV4, qFixedCoordinate, qBox]; positivity
  have h_η : 0 ≤ η_work := by linarith
  have h_zeta : 0 ≤ ζDir p_projective ε κ0 := by dsimp only [ζDir, qProjective]; positivity
  have h_proj : 0 ≤ ηProj L_exp η_work ε κ0 p_projective := by
    dsimp only [ηProj, qProjective]; positivity
  linarith

/-- Corrected extraction gap bridge: `(1 + qBox) * qNormEnergyV3 < εnc / 2`.

Uses the chain:
  `(1 + qBox) * qNorm < 2 * qNorm ≤ 2 * qTotalV4 ≤ 2 * (εnc / 4) = εnc / 2`.

Strictness in the first step comes from `qBox < 1` and `qNorm > 0`. -/
lemma extraction_gap_bridge_enc2
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep εnc : ℝ}
    (hL_nonneg : 0 ≤ L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (h_total : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4)
    (h_qbox : qBox η_work τ < 1)
    (h_norm_pos : 0 < qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep) :
    (1 + qBox η_work τ) * qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep < εnc / 2 := by
  have h_norm_le_total : qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep ≤
      qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep :=
    qNormEnergyV3_le_qTotalV4 hL_nonneg hη_work_pos hε_pos hκ0_pos hp_nonneg
      hτ_pos hrho_sel_nonneg hrho_sep_nonneg
  have h1 : (1 + qBox η_work τ) * qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep <
      2 * qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    have h_qbox_lt_one : qBox η_work τ < 1 := h_qbox
    have h2 : 1 + qBox η_work τ < 2 := by linarith
    have h3 : 0 < qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := h_norm_pos
    nlinarith
  have h4 : 2 * qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep ≤
      2 * qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by gcongr
  have h5 : 2 * qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 2 := by
    linarith [h_total]
  linarith

end ProductLikeIncidence.ProductReduction

end
