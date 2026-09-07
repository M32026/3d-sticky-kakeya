module

/-
# Wire Budgets v3 — Phase1 Generalization with Full Density Propagation

Revised loss ledger per operator audit:
- qInit = 3·ρ_sel + 2η  (replaces 3ε + 2η)
- qDensity = 3·ρ_sel + qG + qAbsorb  (explicit, NOT forced ≤ η)
- qK_V3 = qK + qDensity  (BSG threshold includes density loss)
- qKA = 3η + qAbsorb + qDensity  (comparability includes density)
- qGraphV3 = 22·qK_V3, qEffV3 = 10·qK_V3
- qSizeLossV3 = qEffV3 + (L+7/2)η + qP + qAbsorb  (independent lower-size losses)
- qDiffV3 = 80·qK_V3 + 2·qKA + qAbsorb
- rho_exc = qPlan + η + qKaufman + ρ_sel + qAbsorb  (pays popularity mass c/8)
- qCoordEnergy = rho_exc + 6·ρ_sel + 2κ0·ρ_sep
- qNormEnergy = qCoordEnergy + qEnergy

Default Phase1 choices:
- ρ_sel = 2η + qAbsorb η
- ρ_sep = η/κ0  (Frostman: τ·ρ_sep > 2η, valid when τ > 2κ0)

## Whiteprint node
Helper for `incidence_to_ring_contradiction`.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical

namespace ProductLikeIncidence.ProductReduction

/-! ## Phase1 dual exponents -/

/-- Selection exponent default: ρ_sel = 2η + qAbsorb η. -/
def rhoSelDefault (η : ℝ) : ℝ := 2 * η + qAbsorb η

/-- Separation exponent default: ρ_sep = η/κ0.

    Frostman exclusion: 2η < τ·ρ_sep holds whenever 2κ0 < τ.
    The strict gap (τ/κ0 - 2) > 0 is absorbed by the outer δ₀ choice. -/
def rhoSepDefault (η κ0 : ℝ) : ℝ := η / κ0

/-! ## Revised loss definitions -/

/-- Initial product density loss with selection exponent. -/
def qInitV3 (η rho_sel : ℝ) : ℝ := 3 * rho_sel + 2 * η

/-- Product density loss exponent (NOT forced ≤ η). -/
def qDensityV3 (η ε κ0 p_projective rho_sel : ℝ) : ℝ :=
  3 * rho_sel + qG p_projective ε κ0 + qAbsorb η

/-- BSG threshold exponent including density loss: qK_V3 = qK + qDensity. -/
def qKV3 (L η ε κ0 p_projective rho_sel : ℝ) : ℝ :=
  qK L η ε κ0 p_projective + qDensityV3 η ε κ0 p_projective rho_sel

/-- BSG graph retention loss: qGraphV3 = 22·qK_V3. -/
def qGraphV3 (L η ε κ0 p_projective rho_sel : ℝ) : ℝ :=
  22 * qKV3 L η ε κ0 p_projective rho_sel

/-- BSG effective retention: qEffV3 = 10·qK_V3. -/
def qEffV3 (L η ε κ0 p_projective rho_sel : ℝ) : ℝ :=
  10 * qKV3 L η ε κ0 p_projective rho_sel

/-- Phase3 comparability ratio with density propagation. -/
def qKAV3 (η ε κ0 p_projective rho_sel : ℝ) : ℝ :=
  3 * η + qAbsorb η + qDensityV3 η ε κ0 p_projective rho_sel

/-- Difference bound exponent with revised qKA and qK_V3. -/
def qDiffV3 (L η ε κ0 p_projective rho_sel : ℝ) : ℝ :=
  80 * qKV3 L η ε κ0 p_projective rho_sel
  + 2 * qKAV3 η ε κ0 p_projective rho_sel + qAbsorb η

/-- Size loss exponent with qEffV3 plus independent lower-size losses. -/
def qSizeLossV3 (L η ε κ0 p_projective rho_sel : ℝ) : ℝ :=
  qEffV3 L η ε κ0 p_projective rho_sel
  + (L + 7 / 2) * η + qProjective p_projective ε κ0 + qAbsorb η

/-- Kaufman base threshold: qKaufBase = qPlan + η + qKaufman + qAbsorb. -/
def qKaufBase (η τ κ0 : ℝ) : ℝ :=
  qPlan η + η + qKaufman η τ κ0 + qAbsorb η

/-- Exact Kaufman bad-direction threshold: rho_exc = qKaufBase + rho_sel. -/
def rhoExc (η _ε τ κ0 rho_sel : ℝ) : ℝ :=
  qKaufBase η τ κ0 + rho_sel

/-- Coordinate energy with Phase1 losses. -/
def qCoordEnergyV3 (η ε τ κ0 rho_sel rho_sep : ℝ) : ℝ :=
  rhoExc η ε τ κ0 rho_sel + 6 * rho_sel + 2 * κ0 * rho_sep

/-- Normalized energy exponent. -/
def qNormEnergyV3 (η ε τ κ0 rho_sel rho_sep : ℝ) : ℝ :=
  qCoordEnergyV3 η ε τ κ0 rho_sel rho_sep + qEnergy η τ κ0

/-- Total endgame loss exponent (v3 with full density propagation). -/
def qTotalV3 (L η ε κ0 p_projective τ rho_sel rho_sep : ℝ) : ℝ :=
  qInitV3 η rho_sel
  + qG p_projective ε κ0
  + qGraphV3 L η ε κ0 p_projective rho_sel
  + qAbsorb η
  + 2 * qDiffV3 L η ε κ0 p_projective rho_sel
  + qSizeLossV3 L η ε κ0 p_projective rho_sel
  + η
  + ζDir p_projective ε κ0
  + ηProj L η ε κ0 p_projective
  + qNormEnergyV3 η ε τ κ0 rho_sel rho_sep

/-! ## Coefficient bound -/

/-- Total loss coefficient for v3 (full density propagation). -/
def gapCoefficientV3 (L κ0 p_projective τ : ℝ) : ℝ :=
  192 * (L + 2) + 1828 + 2 * L + 1767 * p_projective / (2 * κ0)
  + 16 * κ0 / τ + κ0 / 25

lemma gapCoefficientV3_pos {L κ0 p_projective τ : ℝ}
    (hL_nonneg : 0 ≤ L) (hκ0_pos : 0 < κ0) (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ) : 0 < gapCoefficientV3 L κ0 p_projective τ := by
  dsimp only [gapCoefficientV3]
  have h1 : 0 < 192 * (L + 2) + 1828 + 2 * L := by linarith
  have h2 : 0 ≤ 1767 * p_projective / (2 * κ0) := by positivity
  have h3 : 0 < 16 * κ0 / τ + κ0 / 25 := by positivity
  linarith

/-- Exact symbolic expansion of qTotalV3. -/
lemma qTotalV3_expansion (L η ε κ0 p_projective τ rho_sel rho_sep : ℝ) :
    qTotalV3 L η ε κ0 p_projective τ rho_sel rho_sep =
    192 * qKV3 L η ε κ0 p_projective rho_sel
    + 13 * qProjective p_projective ε κ0
    + 22 * rho_sel
    + (2 * L + 29 + 64 / 100) * η
    + 2 * κ0 * rho_sep
    + 16 * κ0 / τ * η
    + 4 * κ0 / 100 * η := by
  dsimp only [qTotalV3, qInitV3, qDensityV3, qKV3, qGraphV3, qEffV3, qKAV3, qDiffV3,
    qSizeLossV3, qKaufBase, rhoExc, qCoordEnergyV3, qNormEnergyV3,
    qGraph, qSizeLoss, qEff, qPlan, qKaufman, qEnergy, qBox, qAbsorb, qG, ζDir,
    ηProj, qK, qProjective]
  ; ring

/-- qTotalV3 ≤ gapCoefficientV3 · η.

    Phase1 assumptions: ρ_sel ≤ 3η, ρ_sep ≤ η/κ0. -/
lemma qTotalV3_le_gapCoefficient_mul_η
    {L η ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (_hL_nonneg : 0 ≤ L) (hη_pos : 0 < η) (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0) (hp_nonneg : 0 ≤ p_projective)
    (_hτ_pos : 0 < τ)
    (h_ε_le_three_halves : ε ≤ (3 / 2) * η)
    (hrho_sel_le : rho_sel ≤ 3 * η)
    (hrho_sep_le : rho_sep ≤ η / κ0) :
    qTotalV3 L η ε κ0 p_projective τ rho_sel rho_sep ≤
    gapCoefficientV3 L κ0 p_projective τ * η := by
  set qP : ℝ := qProjective p_projective ε κ0 with hqP_def
  have hqK_eq : qK L η ε κ0 p_projective = (L + 2) * η + qP := by
    simp [qK, qProjective, hqP_def]
  have h_eps_bound : qP ≤ (3 / 2) * p_projective * η / κ0 := by
    simp only [hqP_def, qProjective]
    have h5 : p_projective * ε ≤ p_projective * ((3 / 2) * η) :=
      mul_le_mul_of_nonneg_left h_ε_le_three_halves hp_nonneg
    have h6 : p_projective * ε / κ0 ≤ p_projective * ((3 / 2) * η) / κ0 :=
      div_le_div_of_nonneg_right h5 (by positivity)
    have h7 : p_projective * ((3 / 2) * η) / κ0 = (3 / 2) * p_projective * η / κ0 := by ring
    rw [h7] at h6; exact h6
  have h2 : 4 * κ0 / 100 * η = κ0 / 25 * η := by ring
  have h3 : 598 * rho_sel ≤ 1794 * η := by
    have h : rho_sel ≤ 3 * η := hrho_sel_le; linarith
  have h4 : 2 * κ0 * rho_sep ≤ 2 * η := by
    have h5 : rho_sep ≤ η / κ0 := hrho_sep_le
    have h6 : 2 * κ0 * rho_sep ≤ 2 * κ0 * (η / κ0) := by gcongr
    have h7 : 2 * κ0 * (η / κ0) = 2 * η := by
      field_simp [hκ0_pos.ne']
    rw [h7] at h6; exact h6
  have hqKV3_eq : qKV3 L η ε κ0 p_projective rho_sel =
      (L + 2) * η + 3 * qP + 3 * rho_sel + η / 100 := by
    simp [qKV3, qK, qDensityV3, qG, qProjective, qAbsorb, hqP_def]; ring
  rw [qTotalV3_expansion, h2, hqKV3_eq]
  have h5 : 192 * ((L + 2) * η + 3 * qP + 3 * rho_sel + η / 100) + 13 * qP + 22 * rho_sel
      + (2 * L + 29 + 64 / 100) * η + 2 * κ0 * rho_sep
      + 16 * κ0 / τ * η + κ0 / 25 * η ≤
      192 * ((L + 2) * η) + (1828 + 2 * L) * η +
      589 * ((3 / 2) * p_projective * η / κ0) +
      16 * κ0 / τ * η + κ0 / 25 * η := by
    have h6 : 192 * (3 * qP) + 13 * qP ≤ 589 * ((3 / 2) * p_projective * η / κ0) := by
      have h7 : 192 * (3 * qP) + 13 * qP = 589 * qP := by ring
      rw [h7]
      gcongr
    have h8 : 192 * (3 * rho_sel) + 22 * rho_sel ≤ 1794 * η := by
      have h9 : 192 * (3 * rho_sel) + 22 * rho_sel = 598 * rho_sel := by ring
      rw [h9]
      linarith [h3]
    have h9 : 2 * κ0 * rho_sep ≤ 2 * η := h4
    have h10 : 192 * (η / 100) + (2 * L + 29 + 64 / 100) * η + 1794 * η + 2 * η ≤ (1828 + 2 * L) * η := by
      have h11 : (0 : ℝ) < η := hη_pos
      nlinarith
    nlinarith
  have h12 : 192 * ((L + 2) * η) + (1828 + 2 * L) * η +
      589 * ((3 / 2) * p_projective * η / κ0) +
      16 * κ0 / τ * η + κ0 / 25 * η =
      gapCoefficientV3 L κ0 p_projective τ * η := by
    simp [gapCoefficientV3]; ring
  calc _ ≤ _ := h5
       _ = gapCoefficientV3 L κ0 p_projective τ * η := h12

/-- Budget feasibility: η < εgain / gapCoefficientV3 ⇒ εgain > qTotalV3. -/
theorem budgetV3_feasible
    {εgain L η ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hεgain_pos : 0 < εgain)
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η) (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0) (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (h_ε_le_three_halves : ε ≤ (3 / 2) * η)
    (hrho_sel_le : rho_sel ≤ 3 * η)
    (hrho_sep_le : rho_sep ≤ η / κ0)
    (h_small : η < εgain / gapCoefficientV3 L κ0 p_projective τ) :
    εgain > qTotalV3 L η ε κ0 p_projective τ rho_sel rho_sep := by
  set C : ℝ := gapCoefficientV3 L κ0 p_projective τ with hC_def
  have hC_pos : 0 < C := gapCoefficientV3_pos hL_nonneg hκ0_pos hp_nonneg hτ_pos
  have h1 : qTotalV3 L η ε κ0 p_projective τ rho_sel rho_sep ≤ C * η :=
    qTotalV3_le_gapCoefficient_mul_η hL_nonneg hη_pos hε_pos hκ0_pos hp_nonneg
      hτ_pos h_ε_le_three_halves hrho_sel_le hrho_sep_le
  have h2 : C * η < εgain := by
    have h3 : η < εgain / C := h_small
    have h4 : C * η < C * (εgain / C) := by gcongr
    have h5 : C * (εgain / C) = εgain := by
      field_simp [hC_pos.ne']
    rw [h5] at h4; exact h4
  exact lt_of_le_of_lt h1 h2

/-! ## exists_budgetV3 -/

/-- Frostman exclusion: 2η < τ·ρ_sep when ρ_sep = η/κ0 and 2κ0 < τ.

    The strict gap (τ/κ0 - 2) > 0 is absorbed by the outer δ₀ choice. -/
lemma frostman_condition_strict
    {η κ0 τ : ℝ} (hη_pos : 0 < η) (hκ0_pos : 0 < κ0)
    (h2kappa_lt_tau : 2 * κ0 < τ) :
    2 * η < τ * (η / κ0) := by
  have h1 : 2 * κ0 < τ := h2kappa_lt_tau
  have h2 : (2 : ℝ) < τ / κ0 := by
    calc (2 : ℝ)
      = (2 * κ0) / κ0 := by field_simp [hκ0_pos.ne'] <;> ring
    _ < τ / κ0 := by gcongr
  have h3 : τ * (η / κ0) = (τ / κ0) * η := by ring
  rw [h3]
  exact mul_lt_mul_of_pos_right h2 hη_pos

/-- Existence of valid v3 budget parameters.

    No Phase3 density condition needed (density propagated through qK_V3).
    ε is chosen as (3/2)η for the enlarged qProjective bound.
    η is bounded by κ0 to ensure ρ_sep = η/κ0 ≤ 1. -/
theorem exists_budgetV3
    {εgain L κ0 s p_projective τ : ℝ}
    (hεgain_pos : 0 < εgain)
    (hL_nonneg : 0 ≤ L)
    (hκ0_pos : 0 < κ0)
    (hs_gt_κ0 : κ0 < s)
    (hp_ge_10 : 10 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (h_tau_gt : 2 * κ0 < τ) :
    ∃ (η ε rho_sel rho_sep : ℝ), 0 < η ∧ 0 < ε ∧ 10 * ε < η ∧
      ε ≤ (3 / 2) * η ∧
      5 * η < 2 * (s - κ0) ∧
      4 * η < τ ∧
      η ≤ κ0 ∧
      rho_sel = rhoSelDefault η ∧
      rho_sep = rhoSepDefault η κ0 ∧
      rho_sel ≤ 3 * η ∧
      rho_sep ≤ η / κ0 ∧
      2 * η < τ * rho_sep ∧
      εgain > qTotalV3 L η ε κ0 p_projective τ rho_sel rho_sep := by
  set C : ℝ := gapCoefficientV3 L κ0 p_projective τ with hC_def
  have hC_pos : 0 < C := gapCoefficientV3_pos hL_nonneg hκ0_pos (by linarith) hτ_pos
  have hsκ0_pos : 0 < s - κ0 := by linarith
  set η1 : ℝ := εgain / (2 * C) with hη1_def
  set η2 : ℝ := (s - κ0) / 3 with hη2_def
  set η3 : ℝ := τ / 5 with hη3_def
  set η4 : ℝ := κ0 with hη4_def
  have hη1_pos : 0 < η1 := by positivity
  have hη2_pos : 0 < η2 := by positivity
  have hη3_pos : 0 < η3 := by positivity
  have hη4_pos : 0 < η4 := hκ0_pos
  set η : ℝ := min η1 (min η2 (min η3 η4)) with hη_def
  have hη_pos : 0 < η := by
    exact lt_min hη1_pos (lt_min hη2_pos (lt_min hη3_pos hη4_pos))
  have hη_le_η1 : η ≤ η1 := min_le_left _ _
  have hη_le_η234 : η ≤ min η2 (min η3 η4) := min_le_right _ _
  have hη_le_η2 : η ≤ η2 := le_trans hη_le_η234 (min_le_left _ _)
  have hη_le_η34 : η ≤ min η3 η4 := le_trans hη_le_η234 (min_le_right _ _)
  have hη_le_η3 : η ≤ η3 := le_trans hη_le_η34 (min_le_left _ _)
  have hη_le_η4 : η ≤ η4 := le_trans hη_le_η34 (min_le_right _ _)
  set ε : ℝ := η / 20 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h10ε_lt_η : 10 * ε < η := by
    rw [hε_def] <;> linarith
  have h_ε_le : ε ≤ (3 / 2) * η := by
    rw [hε_def] <;> linarith
  have h5η : 5 * η < 2 * (s - κ0) := by
    have h : η ≤ (s - κ0) / 3 := hη_le_η2
    have h' : 5 * η ≤ 5 * ((s - κ0) / 3) := by gcongr
    have h'' : 5 * ((s - κ0) / 3) < 2 * (s - κ0) := by
      have hpos2 : 0 < s - κ0 := by linarith
      linarith
    linarith
  have h4η : 4 * η < τ := by
    have h : η ≤ τ / 5 := hη_le_η3
    have h' : 4 * η ≤ 4 * (τ / 5) := by gcongr
    have h'' : 4 * (τ / 5) < τ := by
      have hpos2 : 0 < τ := hτ_pos
      linarith
    linarith
  have hη_le_kappa0 : η ≤ κ0 := hη_le_η4
  set rho_sel : ℝ := rhoSelDefault η with hrho_sel_def
  set rho_sep : ℝ := rhoSepDefault η κ0 with hrho_sep_def
  have hrho_sel_le : rho_sel ≤ 3 * η := by
    dsimp only [rho_sel, rhoSelDefault, qAbsorb]; linarith
  have hrho_sep_le : rho_sep ≤ η / κ0 := by
    dsimp only [rho_sep, rhoSepDefault]; exact le_refl _
  have h_frostman : 2 * η < τ * rho_sep := by
    dsimp only [rho_sep, rhoSepDefault]
    exact frostman_condition_strict hη_pos hκ0_pos h_tau_gt
  have h_small : η < εgain / C := by
    have h1 : η ≤ εgain / (2 * C) := hη_le_η1
    have h2 : εgain / (2 * C) < εgain / C := by
      apply div_lt_div_of_pos_left hεgain_pos <;> linarith
    exact lt_of_le_of_lt h1 h2
  exact ⟨η, ε, rho_sel, rho_sep, hη_pos, hε_pos, h10ε_lt_η, h_ε_le, h5η, h4η,
    hη_le_kappa0, rfl, rfl, hrho_sel_le, hrho_sep_le, h_frostman,
    budgetV3_feasible hεgain_pos hL_nonneg hη_pos hε_pos hκ0_pos (by linarith) hτ_pos
      h_ε_le hrho_sel_le hrho_sep_le h_small⟩

/-! ## Supporting lemmas -/

/-- **Phase 3 density condition** (legacy, not used in v3 budget). -/
lemma phase3_density_conditionV3
    {η ε κ0 p_projective : ℝ}
    (hη_pos : 0 < η)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective)
    (hε_def : ε = κ0 * η / (20 * p_projective + 10 * κ0)) :
    3 * ε + qG p_projective ε κ0 + qAbsorb η ≤ η := by
  simp only [hε_def, qG, qProjective, qAbsorb]
  have hpos : 0 < 20 * p_projective + 10 * κ0 := by linarith
  field_simp [hpos.ne', hκ0_pos.ne']
  ; ring_nf; nlinarith

/-- **qDensity identity**: qGraphTotalV3 = qDensity + 2η + qGraphV3. -/
lemma qGraphTotalV3_eq
    {L η ε κ0 p_projective rho_sel : ℝ} :
    qInitV3 η rho_sel + qG p_projective ε κ0 + qGraphV3 L η ε κ0 p_projective rho_sel + qAbsorb η =
      qDensityV3 η ε κ0 p_projective rho_sel + 2 * η + qGraphV3 L η ε κ0 p_projective rho_sel := by
  simp [qInitV3, qDensityV3, qGraphV3, qG, qAbsorb]; ring

/-! ## Terminal budget -/

/-- **Terminal budget lemma** (v3): Produces the exact budget hypothesis. -/
lemma terminal_budgetV3
    {εgain L η ε κ0 p_projective τ rho_sel rho_sep : ℝ}
    (hεgain_pos : 0 < εgain)
    (hL_nonneg : 0 ≤ L)
    (hη_pos : 0 < η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (h_ε_le_three_halves : ε ≤ (3 / 2) * η)
    (hrho_sel_le : rho_sel ≤ 3 * η)
    (hrho_sep_le : rho_sep ≤ η / κ0)
    (h_small : η < εgain / gapCoefficientV3 L κ0 p_projective τ) :
    let q_graph_total := qInitV3 η rho_sel + qG p_projective ε κ0 + qGraphV3 L η ε κ0 p_projective rho_sel + qAbsorb η
    let q_diff := qDiffV3 L η ε κ0 p_projective rho_sel
    let q_size_loss := qSizeLossV3 L η ε κ0 p_projective rho_sel
    let ζ_dir := ζDir p_projective ε κ0
    let η_proj := ηProj L η ε κ0 p_projective
    let q_norm_energy := qNormEnergyV3 η ε τ κ0 rho_sel rho_sep
    εgain > q_graph_total + 2 * q_diff + q_size_loss + η + ζ_dir + η_proj + q_norm_energy := by
  have h : εgain > qTotalV3 L η ε κ0 p_projective τ rho_sel rho_sep :=
    budgetV3_feasible hεgain_pos hL_nonneg hη_pos hε_pos hκ0_pos hp_nonneg hτ_pos
      h_ε_le_three_halves hrho_sel_le hrho_sep_le h_small
  simpa [qTotalV3, qNormEnergyV3] using h

/-- Bundle of basic facts about default WireBudgetsV3 parameter choices.

Given η, ε, κ0, τ with standard hypotheses, proves positivity, bounds,
and the strict Frostman condition for the default Phase1 choices. -/
lemma budget_wiring_facts
    {η ε κ0 τ p_projective : ℝ}
    (hη_pos : 0 < η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hτ_pos : 0 < τ)
    (hp_ge_10 : 10 ≤ p_projective)
    (h2kappa_lt_tau : 2 * κ0 < τ) :
    let rho_sel := rhoSelDefault η
    let rho_sep := rhoSepDefault η κ0
    let rho_exc := rhoExc η ε τ κ0 rho_sel
    let q_box := qBox η τ
    0 < rho_sel ∧
    0 < rho_sep ∧
    0 < rho_exc ∧
    rho_sel ≤ 3 * η ∧
    rho_sep ≤ η / κ0 ∧
    0 < q_box ∧
    2 * η < τ * rho_sep := by
  dsimp only
  set rho_sel : ℝ := rhoSelDefault η with hrho_sel_def
  set rho_sep : ℝ := rhoSepDefault η κ0 with hrho_sep_def
  set q_box : ℝ := qBox η τ with hq_box_def
  have h1 : 0 < rho_sel := by
    dsimp only [rho_sel, rhoSelDefault, qAbsorb]; linarith
  have h2 : 0 < rho_sep := by
    dsimp only [rho_sep, rhoSepDefault]; positivity
  have hq_box_pos : 0 < q_box := by
    dsimp only [q_box, qBox, qAbsorb]; positivity
  have h3 : 0 < rhoExc η ε τ κ0 rho_sel := by
    dsimp only [rhoExc, qKaufBase, qPlan, qKaufman, qAbsorb]
    have hq_kaufman_pos : 0 < 2 * κ0 * q_box := by positivity
    have hq_plan_pos : 0 < 10 * η + η / 100 := by linarith
    linarith
  have h4 : rho_sel ≤ 3 * η := by
    dsimp only [rho_sel, rhoSelDefault, qAbsorb]; linarith
  have h5 : rho_sep ≤ η / κ0 := by
    dsimp only [rho_sep, rhoSepDefault]; exact le_refl _
  have h7 : 2 * η < τ * rho_sep :=
    frostman_condition_strict hη_pos hκ0_pos h2kappa_lt_tau
  exact ⟨h1, h2, h3, h4, h5, hq_box_pos, h7⟩

end ProductLikeIncidence.ProductReduction
