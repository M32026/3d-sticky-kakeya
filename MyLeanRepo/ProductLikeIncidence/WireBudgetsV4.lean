module

/-
# Wire Budgets V4 — Unified Correction (Operator Consolidation)

Per operator correction (2026-08-09), this is the SINGLE authoritative V4 budget file.

## Key principle
Only replace OCCUPANCY-related qProjective with rho_sep. Keep other projective
losses (pole removal, direction transport) as qProjective.

## Density ledger
- qDensityV4 = 3·rho_sel + 2·rho_sep + qAbsorb
- qKV4 = qK + qDensityV4
- qGraphV4 = 22·qKV4 + η_work/2 + η_work/20 (enlarged to absorb BSG constants)
- qEffV4 = 10·qKV4
- qKAV4 = 2·α + qMassV4 + 3·ρ_sel + 2·qAbsorb (enlarged 01-12PDT, +3ρ_sel/2 for α_K K_A route)
- qDiffV4 = 80·qKV4 + 2·qKAV4 + qAbsorb

Raw density power = 3·rho_sel + L_exp·eta_work.
After occupancy + fixed absorption: 3·rho_sel + 2·rho_sep + qAbsorb + L_exp·eta_work.
Fits qKV4 with slack 2·eta_work + qProjective.

## Coordinate size
- alpha_projection = (L_exp/2)·eta_work
- q_mass = 2·rho_sep + qAbsorb
- q_Pbar = 9·eta_work/2 + qAbsorb
- qInputV4 = (L_exp/2 + 21/4)·eta_work + 2·rho_sep + q_fixed_coordinate + (3/2)·rho_sel
- qSizeLossV4 = qEffV4 + qInputV4 + qAbsorb + qBox (normalization charge)

## εnc split
- qTotalV4 ≤ εnc/4
- qBox < 1
- qExtract = qNormEnergyV3 + qBox + qAbsorb ≤ εnc/2
- 10·qKV4 + qAbsorb + q_fixed_terminal ≤ εnc/2

## Whiteprint node
Helper for `incidence_to_ring_contradiction` V4 budget correction.
-/

public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical

namespace ProductLikeIncidence.ProductReduction

/-! ## Density ledger -/

/-- V4 product density loss exponent: `3·ρ_sel + 2·ρ_sep + qAbsorb`. -/
def qDensityV4 (η_work rho_sel rho_sep : ℝ) : ℝ :=
  3 * rho_sel + 2 * rho_sep + qAbsorb η_work

/-- V4 BSG threshold exponent: `qK + qDensityV4`. -/
def qKV4 (L_exp η_work ε κ0 p_projective rho_sel rho_sep : ℝ) : ℝ :=
  qK L_exp η_work ε κ0 p_projective + qDensityV4 η_work rho_sel rho_sep

/-- V4 BSG graph retention loss, enlarged by `η_work/2 + η_work/20` to absorb BSG constant factors.

The extra exponent ensures `δ^{22·q_K}/(16·3^{22}·28·C_work'^2) ≥ δ^{qGraphV4}` for small δ,
so the recalibrated c_proj still satisfies `hc_proj_ge`. -/
def qGraphV4 (L_exp η_work ε κ0 p_projective rho_sel rho_sep : ℝ) : ℝ :=
  22 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + η_work / 2 + η_work / 20

/-- V4 BSG effective retention. -/
def qEffV4 (L_exp η_work ε κ0 p_projective rho_sel rho_sep : ℝ) : ℝ :=
  10 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep

/-! ## Density fit proof -/

/-- V4 c_dense exponent fits qKV4 with slack `2·η_work + qProjective > 0`.

The density exponent after occupancy absorption is
`3·ρ_sel + 2·ρ_sep + qAbsorb + L_exp·η_work`, which is strictly less than qKV4. -/
lemma c_dense_exp_le_qKV4
    {L_exp η_work ε κ0 p_projective rho_sel rho_sep : ℝ}
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective) :
    3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work ≤
      qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep := by
  dsimp only [qKV4, qDensityV4, qK, qProjective]
  have h : 0 ≤ 2 * η_work + p_projective * ε / κ0 := by positivity
  linarith

/-! ## Coordinate size -/

/-- Coordinate projection exponent: `α = (L_exp/2)·η_work`. -/
def alphaProjectionV4 (L_exp η_work : ℝ) : ℝ :=
  (L_exp / 2) * η_work

/-- Mass transfer exponent: `q_mass = 2·ρ_sep + qAbsorb`. -/
def qMassV4 (η_work rho_sep : ℝ) : ℝ :=
  2 * rho_sep + qAbsorb η_work

/-- V4 Phase3 comparability ratio (enlarged, operator correction 01-12PDT).

Directly dominates the no-occupancy cardinal K_A route:
`2·α + qMassV4 + (3/2)·ρ_sel + 2·qAbsorb`, keeping the `2·ρ_sep` occupancy loss. -/
def qKAV4 (L_exp η_work rho_sel rho_sep : ℝ) : ℝ :=
  2 * alphaProjectionV4 L_exp η_work
  + qMassV4 η_work rho_sep
  + 3 * rho_sel
  + 2 * qAbsorb η_work

/-- Normalization chunk loss: `qGraphV4 + qBox + qAbsorb`.

Post-BSG weighted normalization loses `c_graph/(4*(2R+1))`, where
`c_graph ≈ δ^{qGraphV4}` and `2R+1 ≈ δ^{-qBox}`. This chunk charges
both the graph-density inverse retention and the tube-radius factor.
-/
def qNormChunkV4 (L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ) : ℝ :=
  qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
  + qBox η_work τ + qAbsorb η_work

/-- V4 difference bound exponent, enlarged by qNormChunkV4 for normalized regularity. -/
def qDiffV4 (L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ) : ℝ :=
  80 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
  + 2 * qKAV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work
  + qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep

/-- Pbar covering exponent: `q_Pbar = 9·η_work/2 + qAbsorb`. -/
def qPbarV4 (η_work : ℝ) : ℝ :=
  9 * η_work / 2 + qAbsorb η_work

/-- Fixed coordinate absorption exponent. Set to `3·qAbsorb` to absorb
the three qAbsorb contributions in the coordinate β expansion. -/
def qFixedCoordinate (η_work : ℝ) : ℝ := 3 * qAbsorb η_work

/-- V4 coordinate size input budget. -/
def qInputV4 (L_exp η_work rho_sel rho_sep : ℝ) : ℝ :=
  (L_exp / 2 + 21 / 4) * η_work + 2 * rho_sep + qFixedCoordinate η_work + (3 * rho_sel) / 2

/-- V4 size loss exponent: `qEffV4 + qInputV4 + qAbsorb + qNormChunkV4`.

The `qNormChunkV4` charge accounts for the full post-BSG normalization
loss: graph-density inverse retention (`qGraphV4`) plus tube-radius
factor (`qBox`) plus fixed absorption. -/
def qSizeLossV4 (L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ) : ℝ :=
  qEffV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
  + qInputV4 L_exp η_work rho_sel rho_sep + qAbsorb η_work
  + qNormChunkV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep

/-! ## Coordinate fit proof -/

/-- Coordinate β expansion.

With `q_ret = 3·ρ_sel` (threefold retention):
  β = α + q_mass + q_ret/2 + q_Pbar/2
  = (L_exp/2 + 21/4)·η_work + 2·ρ_sep + 3·qAbsorb
  ≤ qInputV4
-/
lemma coordinate_beta_le_qInputV4
    {L_exp η_work rho_sel rho_sep : ℝ}
    (hη_work_pos : 0 < η_work)
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work) :
    alphaProjectionV4 L_exp η_work + qMassV4 η_work rho_sep
      + (3 * rho_sel) / 2 + (qPbarV4 η_work) / 2
    ≤ qInputV4 L_exp η_work rho_sel rho_sep := by
  dsimp only [alphaProjectionV4, qMassV4, qPbarV4, qInputV4, qFixedCoordinate]
  rw [hrho_sel_eq]
  simp only [rhoSelDefault, qAbsorb]
  have h_eq : L_exp / 2 * η_work + (2 * rho_sep + η_work / 100) + 3 * (2 * η_work + η_work / 100) / 2 +
      (9 * η_work / 2 + η_work / 100) / 2 =
    (L_exp / 2 + 21 / 4) * η_work + 2 * rho_sep + 3 * (η_work / 100) := by ring
  have h_extra : 0 ≤ (3 * (2 * η_work + η_work / 100)) / 2 := by positivity
  linarith

/-! ## Total endgame loss -/

/-- V4 total endgame loss exponent. -/
def qTotalV4 (L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ) : ℝ :=
  qInitV3 η_work rho_sel
  + 2 * rho_sep
  + qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep
  + qAbsorb η_work
  + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
  + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
  + η_work
  + ζDir p_projective ε κ0
  + ηProj L_exp η_work ε κ0 p_projective
  + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep

/-- Exact symbolic expansion of qTotalV4. -/
lemma qTotalV4_expansion (L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ) :
    qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep =
    ((527 / 2) * L_exp + 26873 / 50) * η_work
    + 260 * qProjective p_projective ε κ0
    + (1595 / 2 : ℝ) * rho_sel
    + (528 + 2 * κ0) * rho_sep
    + (284 + 4 * κ0) * qAbsorb η_work
    + (16 * κ0 + 12) / τ * η_work := by
  dsimp only [qTotalV4, qInitV3, qGraphV4, qDiffV4, qSizeLossV4, qEffV4,
    qNormChunkV4, qKV4, qDensityV4, qKAV4, qInputV4, qFixedCoordinate,
    qNormEnergyV3, qCoordEnergyV3, rhoExc, qKaufBase,
    qPlan, qKaufman, qEnergy, qBox, qAbsorb, ζDir, ηProj,
    qK, qProjective, alphaProjectionV4, qMassV4]
  <;> field_simp <;> ring

/-- V4 total loss coefficient (includes qNormChunkV4 in qSizeLoss and qDiff). -/
def gapCoefficientV4 (L_exp κ0 p_projective τ : ℝ) : ℝ :=
  (527 / 2) * L_exp + 14674 / 5
  + (390 * p_projective + 528) / κ0
  + (16 * κ0 + 12) / τ
  + κ0 / 25

lemma gapCoefficientV4_pos {L_exp κ0 p_projective τ : ℝ}
    (hL_nonneg : 0 ≤ L_exp) (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective) (hτ_pos : 0 < τ) :
    0 < gapCoefficientV4 L_exp κ0 p_projective τ := by
  dsimp only [gapCoefficientV4]
  have h1 : 0 < (527 / 2 : ℝ) * L_exp + 71171 / 25 := by positivity
  have h2 : 0 ≤ (390 * p_projective + 528) / κ0 := by positivity
  have h3 : 0 < (16 * κ0 + 12) / τ + κ0 / 25 := by positivity
  linarith

/-- qTotalV4 ≤ gapCoefficientV4 · η_work under standard Phase1 bounds. -/
lemma qTotalV4_le_gapCoefficient_mul_η
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (_hL_nonneg : 0 ≤ L_exp) (hη_work_pos : 0 < η_work) (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0) (hp_nonneg : 0 ≤ p_projective)
    (_hτ_pos : 0 < τ)
    (h_ε_le_three_halves : ε ≤ (3 / 2) * η_work)
    (hrho_sel_le : rho_sel ≤ 3 * η_work)
    (hrho_sep_le : rho_sep ≤ η_work / κ0) :
    qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤
      gapCoefficientV4 L_exp κ0 p_projective τ * η_work := by
  set qP : ℝ := qProjective p_projective ε κ0 with hqP_def
  have h_eps_bound : qP ≤ (3 / 2) * p_projective * η_work / κ0 := by
    simp only [hqP_def, qProjective]
    have h4 : p_projective * ε ≤ p_projective * ((3 / 2) * η_work) :=
      mul_le_mul_of_nonneg_left h_ε_le_three_halves hp_nonneg
    have h5 : p_projective * ε / κ0 ≤ p_projective * ((3 / 2) * η_work) / κ0 :=
      div_le_div_of_nonneg_right h4 (by positivity)
    have h6 : p_projective * ((3 / 2) * η_work) / κ0 = (3 / 2) * p_projective * η_work / κ0 := by ring
    rw [h6] at h5; exact h5
  have hqAbsorb_eq : qAbsorb η_work = η_work / 100 := by simp [qAbsorb]
  rw [qTotalV4_expansion, hqAbsorb_eq]
  dsimp only [gapCoefficientV4]
  have h2 : (1595 / 2 : ℝ) * rho_sel ≤ (4785 / 2 : ℝ) * η_work := by linarith
  have h3 : (528 + 2 * κ0) * rho_sep ≤ (528 / κ0 + 2) * η_work := by
    calc
      (528 + 2 * κ0) * rho_sep
        ≤ (528 + 2 * κ0) * (η_work / κ0) := by gcongr
      _ = (528 / κ0 + 2) * η_work := by
        field_simp [hκ0_pos.ne'] <;> ring
  have h4 : (284 + 4 * κ0) * (η_work / 100) = (284 / 100 + κ0 / 25) * η_work := by
    ring
  have h5 : 260 * qP ≤ 390 * p_projective * (η_work / κ0) := by
    calc 260 * qP
      ≤ 260 * ((3 / 2) * p_projective * η_work / κ0) := by gcongr
    _ = 390 * p_projective * (η_work / κ0) := by ring
  have h6 : (528 + 2 * κ0) * rho_sep + 260 * qP ≤
      ((390 * p_projective + 528) / κ0 + 2) * η_work := by
    calc
      (528 + 2 * κ0) * rho_sep + 260 * qP
        ≤ (528 / κ0 + 2) * η_work + 390 * p_projective * (η_work / κ0) := by gcongr
      _ = ((390 * p_projective + 528) / κ0 + 2) * η_work := by
        field_simp [hκ0_pos.ne'] <;> ring
  rw [h4]
  linarith [h2, h6]

/-! ## εnc split -/

/-- Extraction exponent: `qExtract = qNormEnergyV3 + qBox + qAbsorb`. -/
def qExtractV4 (η_work ε τ κ0 rho_sel rho_sep : ℝ) : ℝ :=
  qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep + qBox η_work τ + qAbsorb η_work

/-- Extraction gap: `qNormEnergyV3 + qBox < qExtractV4`. -/
lemma extractionGapV4_pos {η_work ε τ κ0 rho_sel rho_sep : ℝ} (hη_work_pos : 0 < η_work) :
    qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep + qBox η_work τ <
      qExtractV4 η_work ε τ κ0 rho_sel rho_sep := by
  dsimp only [qExtractV4]
  have h : 0 < qAbsorb η_work := by dsimp only [qAbsorb]; positivity
  linarith

/-- Extraction coefficient: `qExtractV4 ≤ C_extract · η_work` with defaults. -/
def extractionCoefficientV4 (κ0 τ : ℝ) : ℝ :=
  27 + (4 + 16 * κ0) / τ + (11 + 4 * κ0) / 100

lemma qExtractV4_le_coefficient
    {η_work ε κ0 τ rho_sel rho_sep : ℝ}
    (hη_work_pos : 0 < η_work) (hκ0_pos : 0 < κ0) (hτ_pos : 0 < τ)
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    (hrho_sep_eq : rho_sep = rhoSepDefault η_work κ0) :
    qExtractV4 η_work ε τ κ0 rho_sel rho_sep ≤
      extractionCoefficientV4 κ0 τ * η_work := by
  dsimp only [qExtractV4, extractionCoefficientV4, qNormEnergyV3, qCoordEnergyV3,
    rhoExc, qKaufBase, qPlan, qKaufman, qEnergy, qBox, qAbsorb]
  rw [hrho_sel_eq, hrho_sep_eq]
  simp only [rhoSelDefault, rhoSepDefault, qAbsorb]
  have h_k0 : 2 * κ0 * (η_work / κ0) = 2 * η_work := by
    field_simp [hκ0_pos.ne'] <;> ring
  rw [h_k0]
  <;> ring_nf <;> field_simp [hτ_pos.ne'] <;> norm_num

/-- BSG overhead coefficient: `10·qKV4 + 2·qAbsorb ≤ C_bsg · η_work` with bounds. -/
def bsgOverheadCoefficientV4 (L_exp κ0 p_projective : ℝ) : ℝ :=
  10 * L_exp + 2753 / 25 + (15 * p_projective + 20) / κ0

lemma bsgOverheadV4_le_coefficient
    {L_exp η_work ε κ0 p_projective rho_sel rho_sep : ℝ}
    (hL_nonneg : 0 ≤ L_exp) (hη_work_pos : 0 < η_work) (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0) (hp_nonneg : 0 ≤ p_projective)
    (h_ε_le_three_halves : ε ≤ (3 / 2) * η_work)
    (hrho_sel_le : rho_sel ≤ 3 * η_work)
    (hrho_sep_le : rho_sep ≤ η_work / κ0) :
    10 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + 2 * qAbsorb η_work ≤
      bsgOverheadCoefficientV4 L_exp κ0 p_projective * η_work := by
  set qP : ℝ := qProjective p_projective ε κ0 with hqP_def
  have h_eps_bound : qP ≤ (3 / 2) * p_projective * η_work / κ0 := by
    simp only [hqP_def, qProjective]
    have h4 : p_projective * ε ≤ p_projective * ((3 / 2) * η_work) :=
      mul_le_mul_of_nonneg_left h_ε_le_three_halves hp_nonneg
    have h5 : p_projective * ε / κ0 ≤ p_projective * ((3 / 2) * η_work) / κ0 :=
      div_le_div_of_nonneg_right h4 (by positivity)
    have h6 : p_projective * ((3 / 2) * η_work) / κ0 = (3 / 2) * p_projective * η_work / κ0 := by ring
    rw [h6] at h5; exact h5
  dsimp only [qKV4, qDensityV4, qK, qProjective, bsgOverheadCoefficientV4, qAbsorb]
  have h2 : 30 * rho_sel ≤ 90 * η_work := by linarith
  have h3' : 20 * rho_sep ≤ (20 / κ0) * η_work := by
    calc
      20 * rho_sep
        ≤ 20 * (η_work / κ0) := by gcongr
      _ = (20 / κ0) * η_work := by field_simp [hκ0_pos.ne'] <;> ring
  have h4 : 10 * (p_projective * ε / κ0) ≤ 15 * (p_projective / κ0) * η_work := by
    have h10 : 10 * ε ≤ 15 * η_work := by linarith
    have h11 : p_projective * (10 * ε) ≤ p_projective * (15 * η_work) :=
      mul_le_mul_of_nonneg_left h10 hp_nonneg
    have h11' : 10 * p_projective * ε ≤ 15 * p_projective * η_work := by
      have h : 10 * p_projective * ε = p_projective * (10 * ε) := by ring
      have h' : 15 * p_projective * η_work = p_projective * (15 * η_work) := by ring
      calc
        10 * p_projective * ε = p_projective * (10 * ε) := h
        _ ≤ p_projective * (15 * η_work) := h11
        _ = 15 * p_projective * η_work := h'.symm
    have h12 : 10 * p_projective * ε / κ0 ≤ 15 * p_projective * η_work / κ0 :=
      div_le_div_of_nonneg_right h11' (by positivity)
    have h13 : 10 * (p_projective * ε / κ0) = 10 * p_projective * ε / κ0 := by ring
    have h14 : 15 * p_projective * η_work / κ0 = 15 * (p_projective / κ0) * η_work := by
      field_simp [hκ0_pos.ne'] <;> ring
    calc
      10 * (p_projective * ε / κ0)
        = 10 * p_projective * ε / κ0 := h13
      _ ≤ 15 * p_projective * η_work / κ0 := h12
      _ = 15 * (p_projective / κ0) * η_work := h14
  have h5 : 10 * (p_projective * ε / κ0) + 20 * rho_sep ≤
      ((15 * p_projective + 20) / κ0) * η_work := by
    calc
      10 * (p_projective * ε / κ0) + 20 * rho_sep
        ≤ 15 * (p_projective / κ0) * η_work + (20 / κ0) * η_work := by gcongr
      _ = ((15 * p_projective + 20) / κ0) * η_work := by
        field_simp [hκ0_pos.ne'] <;> ring
  linarith [h2, h5]

/-- qBox < 1 for sufficiently small η_work. -/
lemma qBox_lt_one {η_work τ : ℝ} (hη_work_pos : 0 < η_work) (hτ_pos : 0 < τ)
    (h_small : η_work < τ / (4 + τ / 100)) :
    qBox η_work τ < 1 := by
  dsimp only [qBox, qAbsorb]
  have h : 4 * η_work / τ + η_work / 100 < 1 := by
    have h5 : 4 * η_work / τ + η_work / 100 = η_work * (4 / τ + 1 / 100) := by ring
    rw [h5]
    have h6 : 4 / τ + 1 / 100 = (400 + τ) / (100 * τ) := by
      field_simp [hτ_pos.ne'] <;> ring
    rw [h6]
    have h7 : η_work * ((400 + τ) / (100 * τ)) < 1 := by
      have h8 : η_work < τ / (4 + τ / 100) := h_small
      have h9 : τ / (4 + τ / 100) = (100 * τ) / (400 + τ) := by
        field_simp [hτ_pos.ne'] <;> ring
      rw [h9] at h8
      have h10 : 0 < (400 + τ) := by linarith
      have h11 : η_work * ((400 + τ) / (100 * τ)) <
          ((100 * τ) / (400 + τ)) * ((400 + τ) / (100 * τ)) := by gcongr
      have h12 : ((100 * τ) / (400 + τ)) * ((400 + τ) / (100 * τ)) = 1 := by
        field_simp [hτ_pos.ne', h10.ne'] <;> ring
      rw [h12] at h11; exact h11
    exact h7
  exact h

/-- Unified V4 budget feasibility: all εnc constraints satisfied simultaneously.

Given εnc > 0, choose η_work small enough to satisfy:
- qTotalV4 ≤ εnc/4
- qExtractV4 ≤ εnc/2
- 10·qKV4 + 2·qAbsorb ≤ εnc/2
- qBox < 1
-/
theorem budgetV4_feasible
    {εnc L_exp η_work ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hεnc_pos : 0 < εnc)
    (hL_nonneg : 0 ≤ L_exp)
    (hη_work_pos : 0 < η_work)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (h_ε_le_three_halves : ε ≤ (3 / 2) * η_work)
    (hrho_sel_eq : rho_sel = rhoSelDefault η_work)
    (hrho_sep_eq : rho_sep = rhoSepDefault η_work κ0)
    (hrho_sel_le : rho_sel ≤ 3 * η_work)
    (hrho_sep_le : rho_sep ≤ η_work / κ0)
    (h_small_total : η_work ≤ εnc / (4 * gapCoefficientV4 L_exp κ0 p_projective τ))
    (h_small_extract : η_work ≤ εnc / (2 * extractionCoefficientV4 κ0 τ))
    (h_small_bsg : η_work ≤ εnc / (2 * bsgOverheadCoefficientV4 L_exp κ0 p_projective))
    (h_small_qbox : η_work < τ / (4 + τ / 100)) :
    qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4 ∧
    qExtractV4 η_work ε τ κ0 rho_sel rho_sep ≤ εnc / 2 ∧
    10 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + 2 * qAbsorb η_work ≤ εnc / 2 ∧
    qBox η_work τ < 1 := by
  have hC_total_pos : 0 < gapCoefficientV4 L_exp κ0 p_projective τ :=
    gapCoefficientV4_pos hL_nonneg hκ0_pos hp_nonneg hτ_pos
  have hC_extract_pos : 0 < extractionCoefficientV4 κ0 τ := by
    dsimp only [extractionCoefficientV4]; positivity
  have hC_bsg_pos : 0 < bsgOverheadCoefficientV4 L_exp κ0 p_projective := by
    dsimp only [bsgOverheadCoefficientV4]; positivity
  have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤
      gapCoefficientV4 L_exp κ0 p_projective τ * η_work :=
    qTotalV4_le_gapCoefficient_mul_η hL_nonneg hη_work_pos hε_pos hκ0_pos hp_nonneg
      hτ_pos h_ε_le_three_halves hrho_sel_le hrho_sep_le
  have h1' : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 4 := by
    calc
      gapCoefficientV4 L_exp κ0 p_projective τ * η_work
        ≤ gapCoefficientV4 L_exp κ0 p_projective τ * (εnc / (4 * gapCoefficientV4 L_exp κ0 p_projective τ)) :=
          by gcongr
      _ = εnc / 4 := by
        field_simp [hC_total_pos.ne'] <;> ring
  have h2 : qExtractV4 η_work ε τ κ0 rho_sel rho_sep ≤
      extractionCoefficientV4 κ0 τ * η_work :=
    qExtractV4_le_coefficient hη_work_pos hκ0_pos hτ_pos hrho_sel_eq hrho_sep_eq
  have h2' : extractionCoefficientV4 κ0 τ * η_work ≤ εnc / 2 := by
    calc
      extractionCoefficientV4 κ0 τ * η_work
        ≤ extractionCoefficientV4 κ0 τ * (εnc / (2 * extractionCoefficientV4 κ0 τ)) := by gcongr
      _ = εnc / 2 := by field_simp [hC_extract_pos.ne'] <;> ring
  have h3 : 10 * qKV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + 2 * qAbsorb η_work ≤
      bsgOverheadCoefficientV4 L_exp κ0 p_projective * η_work :=
    bsgOverheadV4_le_coefficient hL_nonneg hη_work_pos hε_pos hκ0_pos hp_nonneg
      h_ε_le_three_halves hrho_sel_le hrho_sep_le
  have h3' : bsgOverheadCoefficientV4 L_exp κ0 p_projective * η_work ≤ εnc / 2 := by
    calc
      bsgOverheadCoefficientV4 L_exp κ0 p_projective * η_work
        ≤ bsgOverheadCoefficientV4 L_exp κ0 p_projective *
            (εnc / (2 * bsgOverheadCoefficientV4 L_exp κ0 p_projective)) := by gcongr
      _ = εnc / 2 := by field_simp [hC_bsg_pos.ne'] <;> ring
  have h4 : qBox η_work τ < 1 := qBox_lt_one hη_work_pos hτ_pos h_small_qbox
  exact ⟨le_trans h1 h1', le_trans h2 h2', le_trans h3 h3', h4⟩

/-! ## Increased q_graph_total budget -/

/-- The enlarged `q_graph_total' = qGraphV4 + η_work` still fits within qTotalV4.

When `q_graph_total` is enlarged by `η_work` to absorb `C_work'^2 ~ δ^{-η_work}`
in `hc_proj_ge'`, the V2 endgame sum increases by exactly `η_work`. This lemma
proves the enlarged sum remains bounded by `qTotalV4`, with gap at least `η_work`.

The key reason: `qInitV3 = 3·ρ_sel + 2·η_work ≥ 2·η_work`, so even after
subtracting `η` (with `η ≤ η_work`), the gap is positive. -/
lemma qGraphV4_increased_le_qTotalV4
    {L_exp η_work ε κ0 p_projective τ rho_sel rho_sep η : ℝ}
    (hη_work_pos : 0 < η_work)
    (hL_nonneg : 0 ≤ L_exp)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (hrho_sel_nonneg : 0 ≤ rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hη_le : η ≤ η_work) :
    qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + η_work
    + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
    + η + ζDir p_projective ε κ0
    + ηProj L_exp η ε κ0 p_projective
    ≤ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  have h_gap_eq : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep -
      (qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + η_work
        + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        + η + ζDir p_projective ε κ0
        + ηProj L_exp η ε κ0 p_projective) =
      qInitV3 η_work rho_sel + 2 * rho_sep + qAbsorb η_work - η
      + (ηProj L_exp η_work ε κ0 p_projective - ηProj L_exp η ε κ0 p_projective)
      + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    dsimp only [qTotalV4, qGraphV4, qDiffV4, qSizeLossV4, ζDir]
    <;> ring
  have h1 : qInitV3 η_work rho_sel ≥ 2 * η_work := by
    dsimp only [qInitV3]; linarith
  have h2 : 0 ≤ ηProj L_exp η_work ε κ0 p_projective - ηProj L_exp η ε κ0 p_projective := by
    dsimp only [ηProj, qProjective]
    have h21 : 0 ≤ L_exp * (η_work - η) := mul_nonneg hL_nonneg (by linarith)
    linarith
  have h3 : 0 ≤ qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    dsimp only [qNormEnergyV3, qCoordEnergyV3, rhoExc, qKaufBase, qPlan, qKaufman, qEnergy, qAbsorb, qBox]
    have h31 : 0 ≤ 4 * η_work / τ + η_work / 100 := by positivity
    positivity
  have h4 : 0 ≤ qInitV3 η_work rho_sel + 2 * rho_sep + qAbsorb η_work - η
      + (ηProj L_exp η_work ε κ0 p_projective - ηProj L_exp η ε κ0 p_projective)
      + qNormEnergyV3 η_work ε τ κ0 rho_sel rho_sep := by
    have h5 : qInitV3 η_work rho_sel - η ≥ η_work := by linarith [h1]
    have h6 : 0 ≤ qAbsorb η_work := by dsimp only [qAbsorb]; positivity
    linarith
  have h5 : 0 ≤ qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep -
      (qGraphV4 L_exp η_work ε κ0 p_projective rho_sel rho_sep + η_work
        + 2 * qDiffV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        + qSizeLossV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep
        + η + ζDir p_projective ε κ0
        + ηProj L_exp η ε κ0 p_projective) := by
    rw [h_gap_eq]; exact h4
  exact le_of_sub_nonneg h5

/-! ## Phase7 Direction Mass Parameter -/

/-- Phase7 bad-direction Frostman mass exponent.

This is DISTINCT from `ε_sel` (the small Kaufman/energy selection threshold
with `10·ε_sel < η_work`). The double counting argument gives direction mass
`~δ^{3η}`, so `ε_dir = 3·η_work`.

Used by `sector_absorb_edir` and `frostman_budget_edir` in Phase7Budgets. -/
def epsilonDirV4 (η_work : ℝ) : ℝ := 3 * η_work

/-! ## exists_budgetV4 -/

/-- Existence of valid V4 budget parameters.

Given structural parameters and the non-critical budget εnc, returns
η_work, ε, ρ_sel, ρ_sep, εgain satisfying:
- Base structural conditions (5η_work < 2(s-κ0), 4η_work < τ, η_work ≤ κ0, etc.)
- V4 feasibility conditions for budgetV4_feasible
- εgain > qTotalV4
- 10ε < η_work
- η_work / 2 ≤ η_nc
-/
theorem exists_budgetV4
    {s τ κ0 εnc η_nc L_exp p_projective εgain_ring : ℝ}
    (hτ_pos : 0 < τ)
    (hκ0_pos : 0 < κ0)
    (hs_gt_κ0 : κ0 < s)
    (h2kappa_lt_tau : 2 * κ0 < τ)
    (hεnc_pos : 0 < εnc)
    (hη_nc_pos : 0 < η_nc)
    (hL_nonneg : 0 ≤ L_exp)
    (hp_ge_10 : 10 ≤ p_projective)
    (hεgain_ring_pos : 0 < εgain_ring) :
    ∃ (η_work ε rho_sel rho_sep εgain : ℝ),
      0 < η_work ∧
      0 < ε ∧
      0 < εgain ∧
      εgain ≤ εgain_ring ∧
      10 * ε < η_work ∧
      ε ≤ (3 / 2) * η_work ∧
      5 * η_work < 2 * (s - κ0) ∧
      4 * η_work < τ ∧
      η_work ≤ κ0 ∧
      η_work ≤ 2 * η_nc ∧
      rho_sel = rhoSelDefault η_work ∧
      rho_sep = rhoSepDefault η_work κ0 ∧
      rho_sel ≤ 3 * η_work ∧
      rho_sep ≤ η_work / κ0 ∧
      2 * η_work < τ * rho_sep ∧
      η_work ≤ εnc / (4 * gapCoefficientV4 L_exp κ0 p_projective τ) ∧
      η_work ≤ εnc / (2 * extractionCoefficientV4 κ0 τ) ∧
      η_work ≤ εnc / (2 * bsgOverheadCoefficientV4 L_exp κ0 p_projective) ∧
      η_work < τ / (4 + τ / 100) ∧
      εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
  set C_total : ℝ := gapCoefficientV4 L_exp κ0 p_projective τ with hC_total_def
  set C_extract : ℝ := extractionCoefficientV4 κ0 τ with hC_extract_def
  set C_bsg : ℝ := bsgOverheadCoefficientV4 L_exp κ0 p_projective with hC_bsg_def

  have hC_total_pos : 0 < C_total :=
    gapCoefficientV4_pos hL_nonneg hκ0_pos (by linarith) hτ_pos
  have hC_extract_pos : 0 < C_extract := by
    dsimp only [C_extract, extractionCoefficientV4] <;> positivity
  have hC_bsg_pos : 0 < C_bsg := by
    dsimp only [C_bsg, bsgOverheadCoefficientV4] <;> positivity

  have hsκ0_pos : 0 < s - κ0 := by linarith

  set η1 : ℝ := εnc / (4 * C_total) with hη1_def
  set η2 : ℝ := εnc / (2 * C_extract) with hη2_def
  set η3 : ℝ := εnc / (2 * C_bsg) with hη3_def
  set η4 : ℝ := (τ / (4 + τ / 100)) / 2 with hη4_def
  set η5 : ℝ := (s - κ0) / 3 with hη5_def
  set η6 : ℝ := τ / 5 with hη6_def
  set η7 : ℝ := κ0 with hη7_def
  set η8 : ℝ := 2 * η_nc with hη8_def
  set η9 : ℝ := εgain_ring / (4 * C_total) with hη9_def

  have hη1_pos : 0 < η1 := by positivity
  have hη2_pos : 0 < η2 := by positivity
  have hη3_pos : 0 < η3 := by positivity
  have hη4_pos : 0 < η4 := by positivity
  have hη5_pos : 0 < η5 := by positivity
  have hη6_pos : 0 < η6 := by positivity
  have hη7_pos : 0 < η7 := hκ0_pos
  have hη8_pos : 0 < η8 := by positivity
  have hη9_pos : 0 < η9 := by positivity

  set η_work : ℝ := min η1 (min η2 (min η3 (min η4 (min η5 (min η6 (min η7 (min η8 η9)))))))
    with hη_work_def

  have hη_work_pos : 0 < η_work := by
    rw [hη_work_def]
    have h1 : 0 < min η8 η9 := lt_min hη8_pos hη9_pos
    have h2 : 0 < min η7 (min η8 η9) := lt_min hη7_pos h1
    have h3 : 0 < min η6 (min η7 (min η8 η9)) := lt_min hη6_pos h2
    have h4 : 0 < min η5 (min η6 (min η7 (min η8 η9))) := lt_min hη5_pos h3
    have h5 : 0 < min η4 (min η5 (min η6 (min η7 (min η8 η9)))) := lt_min hη4_pos h4
    have h6 : 0 < min η3 (min η4 (min η5 (min η6 (min η7 (min η8 η9))))) := lt_min hη3_pos h5
    have h7 : 0 < min η2 (min η3 (min η4 (min η5 (min η6 (min η7 (min η8 η9)))))) := lt_min hη2_pos h6
    exact lt_min hη1_pos h7

  have hη_le_η1 : η_work ≤ η1 := min_le_left _ _
  have hη_le_η23 : η_work ≤ min η2 (min η3 (min η4 (min η5 (min η6 (min η7 (min η8 η9)))))) :=
    min_le_right _ _
  have hη_le_η2 : η_work ≤ η2 := le_trans hη_le_η23 (min_le_left _ _)
  have hη_le_η34 : η_work ≤ min η3 (min η4 (min η5 (min η6 (min η7 (min η8 η9))))) :=
    le_trans hη_le_η23 (min_le_right _ _)
  have hη_le_η3 : η_work ≤ η3 := le_trans hη_le_η34 (min_le_left _ _)
  have hη_le_η45 : η_work ≤ min η4 (min η5 (min η6 (min η7 (min η8 η9)))) :=
    le_trans hη_le_η34 (min_le_right _ _)
  have hη_le_η4 : η_work ≤ η4 := le_trans hη_le_η45 (min_le_left _ _)
  have hη_le_η56 : η_work ≤ min η5 (min η6 (min η7 (min η8 η9))) :=
    le_trans hη_le_η45 (min_le_right _ _)
  have hη_le_η5 : η_work ≤ η5 := le_trans hη_le_η56 (min_le_left _ _)
  have hη_le_η67 : η_work ≤ min η6 (min η7 (min η8 η9)) :=
    le_trans hη_le_η56 (min_le_right _ _)
  have hη_le_η6 : η_work ≤ η6 := le_trans hη_le_η67 (min_le_left _ _)
  have hη_le_η78 : η_work ≤ min η7 (min η8 η9) := le_trans hη_le_η67 (min_le_right _ _)
  have hη_le_η7 : η_work ≤ η7 := le_trans hη_le_η78 (min_le_left _ _)
  have hη_le_η89 : η_work ≤ min η8 η9 := le_trans hη_le_η78 (min_le_right _ _)
  have hη_le_η8 : η_work ≤ η8 := le_trans hη_le_η89 (min_le_left _ _)
  have hη_le_η9 : η_work ≤ η9 := le_trans hη_le_η89 (min_le_right _ _)

  set ε : ℝ := η_work / 20 with hε_def
  set rho_sel : ℝ := rhoSelDefault η_work with hrho_sel_def
  set rho_sep : ℝ := rhoSepDefault η_work κ0 with hrho_sep_def
  set εgain : ℝ := εgain_ring / 2 with hεgain_def

  have hε_pos : 0 < ε := by positivity
  have hεgain_pos : 0 < εgain := by positivity
  have h10ε_lt_η : 10 * ε < η_work := by
    rw [hε_def]; linarith
  have h_ε_le : ε ≤ (3 / 2) * η_work := by
    rw [hε_def]; linarith

  have h5η : 5 * η_work < 2 * (s - κ0) := by
    have h : η_work ≤ (s - κ0) / 3 := hη_le_η5
    have h' : 5 * η_work ≤ 5 * ((s - κ0) / 3) := by gcongr
    have h'' : 5 * ((s - κ0) / 3) < 2 * (s - κ0) := by
      have hpos : 0 < s - κ0 := by linarith
      linarith
    linarith

  have h4η : 4 * η_work < τ := by
    have h : η_work ≤ τ / 5 := hη_le_η6
    have h' : 4 * η_work ≤ 4 * (τ / 5) := by gcongr
    have h'' : 4 * (τ / 5) < τ := by
      have hpos : 0 < τ := hτ_pos
      linarith
    linarith

  have hη_le_kappa0 : η_work ≤ κ0 := hη_le_η7
  have hη_le_2ηnc : η_work ≤ 2 * η_nc := hη_le_η8

  have hrho_sel_le : rho_sel ≤ 3 * η_work := by
    dsimp only [rho_sel, rhoSelDefault, qAbsorb]; linarith
  have hrho_sep_le : rho_sep ≤ η_work / κ0 := by
    dsimp only [rho_sep, rhoSepDefault]; exact le_refl _

  have h_frostman : 2 * η_work < τ * rho_sep := by
    dsimp only [rho_sep, rhoSepDefault]
    exact frostman_condition_strict hη_work_pos hκ0_pos h2kappa_lt_tau

  have h_small_qbox : η_work < τ / (4 + τ / 100) := by
    have h1 : η_work ≤ (τ / (4 + τ / 100)) / 2 := hη_le_η4
    have h2 : (τ / (4 + τ / 100)) / 2 < τ / (4 + τ / 100) := by
      apply half_lt_self; positivity
    exact lt_of_le_of_lt h1 h2

  have h_small_total : η_work ≤ εnc / (4 * C_total) := hη_le_η1
  have h_small_extract : η_work ≤ εnc / (2 * C_extract) := hη_le_η2
  have h_small_bsg : η_work ≤ εnc / (2 * C_bsg) := hη_le_η3

  have hV4 := budgetV4_feasible
    (hεnc_pos := hεnc_pos)
    (hL_nonneg := hL_nonneg)
    (hη_work_pos := hη_work_pos)
    (hε_pos := hε_pos)
    (hκ0_pos := hκ0_pos)
    (hp_nonneg := by linarith)
    (hτ_pos := hτ_pos)
    (h_ε_le_three_halves := h_ε_le)
    (hrho_sel_eq := by rfl)
    (hrho_sep_eq := by rfl)
    (hrho_sel_le := hrho_sel_le)
    (hrho_sep_le := hrho_sep_le)
    (h_small_total := h_small_total)
    (h_small_extract := h_small_extract)
    (h_small_bsg := h_small_bsg)
    (h_small_qbox := h_small_qbox)

  have h_qTotal_le_enc4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εnc / 4 :=
    hV4.1

  -- Ring gain budget: qTotalV4 ≤ εgain_ring / 4 via η9
  have h_qTotal_le_gain4 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εgain_ring / 4 := by
    have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ C_total * η_work :=
      qTotalV4_le_gapCoefficient_mul_η hL_nonneg hη_work_pos hε_pos hκ0_pos (by linarith)
        hτ_pos h_ε_le hrho_sel_le hrho_sep_le
    have h2 : C_total * η_work ≤ C_total * η9 := by gcongr
    have h3 : C_total * η9 = εgain_ring / 4 := by
      rw [hη9_def]
      field_simp [hC_total_pos.ne'] <;> ring
    rw [h3] at h2
    exact le_trans h1 h2

  have h_quarter_lt_half : εgain_ring / 4 < εgain_ring / 2 := by
    have h : 0 < εgain_ring := hεgain_ring_pos
    linarith

  have h_εgain_gt : εgain > qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep := by
    have h1 : qTotalV4 L_exp η_work ε κ0 p_projective τ rho_sel rho_sep ≤ εgain_ring / 4 :=
      h_qTotal_le_gain4
    have h2 : εgain_ring / 4 < εgain := by
      simpa [hεgain_def] using h_quarter_lt_half
    exact lt_of_le_of_lt h1 h2

  have hεgain_le_ring : εgain ≤ εgain_ring := by
    rw [hεgain_def]
    linarith [hεgain_ring_pos]

  exact ⟨η_work, ε, rho_sel, rho_sep, εgain,
    hη_work_pos, hε_pos, hεgain_pos, hεgain_le_ring, h10ε_lt_η, h_ε_le, h5η, h4η,
    hη_le_kappa0, hη_le_2ηnc, rfl, rfl, hrho_sel_le, hrho_sep_le, h_frostman,
    h_small_total, h_small_extract, h_small_bsg, h_small_qbox, h_εgain_gt⟩

end ProductLikeIncidence.ProductReduction
