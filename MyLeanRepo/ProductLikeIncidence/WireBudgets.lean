module

/-
# Wire Budgets — Quantitative Composition Loss Ledger

Proves the terminal budget inequality required by Phase 9:
```
εgain > q_graph_total + 2*q_diff + q_A + ζ_dir + η_proj + q_Kaufman + q_energy
```

All loss exponents scale linearly with η. Since εgain > 0 is fixed by the
Ring theorem (WeakTwoEndsSumProduct), choosing η sufficiently small makes
the gap positive.

## Exponent sources

| Exponent | Source | Phase |
|----------|--------|-------|
| q_graph_total = q_init + q_G + 22·q_K + q_absorb | BSG graph retention + constants | 5 |
| q_diff = 80·q_K + 2·q_KA + q_absorb | Ruzsa difference bounds (K_BSG_B2) | 6 |
| q_KA = 3η + q_absorb | Phase 3 comparability ratio | 3 |
| q_A = 10·q_K + 2η | A-set constant enlargement | 3-4 |
| ζ_dir = qProjective | Direction transport chart Lipschitz | 7 |
| η_proj = L·η + qProjective | FullLambda projection transfer | 2,7 |
| q_box = 4η/τ + q_absorb | Quantitative box bound for popular parameter cubes | 0 |
| q_Kaufman = 2κ0·q_box | Kaufman R^{2κ0} bad-direction constant | 1 |
| q_energy = 2κ0·q_box | Normalized coordinate-energy loss | 2 |
| q_bad = 3ε + q_energy + q_Kaufman | Bad-direction energy threshold | 4 |
| η_energy = q_energy + q_Kaufman | Total energy extraction loss | 2-4 |

where q_K = (L+2)·η + p·ε/κ0 is the BSG threshold exponent.

## Feasibility

The total loss is bounded by C·η where C = gapCoefficient(L, κ0, p, τ).
Choosing η < εgain / C gives εgain > total loss.

## Whiteprint node
Helper for `incidence_to_ring_contradiction`.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical

namespace ProductLikeIncidence.ProductReduction

/-! ## Loss exponent definitions -/

/-- Projective normalization loss exponent. -/
def qProjective (p_projective ε κ0 : ℝ) : ℝ :=
  p_projective * ε / κ0

/-- BSG threshold exponent: q_K = (L+2)η + qProjective. -/
def qK (L η ε κ0 p_projective : ℝ) : ℝ :=
  (L + 2) * η + qProjective p_projective ε κ0

/-- BSG graph retention loss: q_graph_total = 22·q_K. -/
def qGraph (L η ε κ0 p_projective : ℝ) : ℝ :=
  22 * qK L η ε κ0 p_projective

/-- A-set δ-set constant enlargement loss: q_A = 10·q_K + 2η. -/
def qA (L η ε κ0 p_projective : ℝ) : ℝ :=
  10 * qK L η ε κ0 p_projective + 2 * η

/-- Graph density loss from covering transfer: q_G = 2·qProjective.

    The M_G covering expansion factor (2·L_G·√2+6)² scales as δ^{-2·qProjective}.
    Product density contains 1/M_G, so this loss must be included before BSG
    retention. -/
def qG (p_projective ε κ0 : ℝ) : ℝ :=
  2 * qProjective p_projective ε κ0

/-- Direction transport chart Lipschitz loss.
    Bounded by qProjective for a bi-Lipschitz chart with constant δ^{-qProjective}. -/
def ζDir (p_projective ε κ0 : ℝ) : ℝ :=
  qProjective p_projective ε κ0

/-- FullLambda projection bound transfer loss: η_proj = L·η + qProjective. -/
def ηProj (L η ε κ0 p_projective : ℝ) : ℝ :=
  L * η + qProjective p_projective ε κ0

/-- Initial product density loss: q_init = 3ε + 2η.

    From fjord's ProductDensityFromThreefold: the product density lower bound
    carries a factor δ^{3ε+2η} from the threefold recursive direction selection
    (3ε) and the fiber δ-set enlargement (2η). -/
def qInit (ε η : ℝ) : ℝ :=
  3 * ε + 2 * η

/-- Numerical constant absorption margin: q_absorb = η/100.

    For any fixed numerical constant C, δ sufficiently small gives
    C ≤ δ^{-q_absorb}, so constants can be absorbed into exponents. -/
def qAbsorb (η : ℝ) : ℝ :=
  η / 100

/-- BSG effective retention exponent: q_eff = 10·q_K.

    From the BSG theorem, the effective threshold retention carries
    exponent 10·q_K. -/
def qEff (L η ε κ0 p_projective : ℝ) : ℝ :=
  10 * qK L η ε κ0 p_projective

/-- Size loss exponent: qSizeLoss = qEff + (L+7/2)·η + qProjective + qAbsorb.

    This is the actual loss from the ideal δ^{-s} lower bound on N(B2).
    Decomposition (verified from phase source outputs):
    - 9η/2 = 5η/2 (Phase0 sqrt) + 2η (Phase3 lower) + η (Phase3 upper)
    - qEff = 10·q_K (BSG retention)
    - (L-1)η (extra projection scale beyond base η)
    - qProjective (projective covering expansion C_q1)
    - qAbsorb (numerical constant absorption)

    Thus N(B2) ≥ const · δ^{-s+qSizeLoss}, and the terminal budget must
    account for qSizeLoss + η in place of the old qA. -/
def qSizeLoss (L η ε κ0 p_projective : ℝ) : ℝ :=
  qEff L η ε κ0 p_projective + (L + 7 / 2) * η + qProjective p_projective ε κ0 + qAbsorb η

/-- Comparability ratio exponent from Phase 3: q_KA = 3η + q_absorb.

    From Phase 3 energy-to-Frostman extraction:
      U ≤ δ^{-η} · sqrt(N(E))    (projection upper bound)
      L ≥ δ^{2η+q_absorb} · sqrt(N(E))    (mass capture lower bound;
        numerical constant (1/2)/C_triv/C2 absorbed into q_absorb)
    Therefore K_A = U/L ≤ δ^{-(3η+q_absorb)}.

    This replaces the incorrect qRatio = qProjective. -/
def qKA (η : ℝ) : ℝ :=
  3 * η + qAbsorb η

/-- Difference bound exponent: q_diff = 80·q_K + 2·q_KA + q_absorb.

    Derived from bacon's exact K_BSG exponent calculation:
    - K_sector dominant = 81·K_eff³·K_KA → 70·q_K
    - K_BSG_B2 = K_sector·K_KA² → 80·q_K + 2·q_KA
    - q_KA = 3η + q_absorb (Phase 3 comparability ratio)
    - q_absorb = η/100 (numerical constant absorption)

    Note: q_KA = 3η + η/100 is dominated by q_K = (L+2)η + qProjective
    for L ≥ 1 and qProjective ≥ η/100 (which holds for the parameter choices
    in exists_budget). Therefore q_diff ≤ 82·q_K + q_absorb under these conditions. -/
def qDiff (L η ε κ0 p_projective : ℝ) : ℝ :=
  80 * qK L η ε κ0 p_projective + 2 * qKA η + qAbsorb η

/-- Quantitative box bound exponent: q_box = 4η/τ + q_absorb.

    From the quantitative box theorem (`quantitative_box_from_popular_cubes`),
    popular parameter cubes lie in a box of radius
    R ≤ (1 + O(δ)) / (c/C_F)^{1/τ} + O(1).

    When Y has Frostman constant C_F = δ^{-η} and the popularity threshold c
    is a fixed constant, the precise calculation gives:
      C_F = 3·C·2^τ, c_box = δ^η / (14·C²)
      C_F / c_box ≤ 42·2^τ·δ^{-4η}
      R ≤ const · (C_F/c_box)^{1/τ} ≤ const · δ^{-4η/τ}

    Absorbing the numerical constant (42·2^τ)^{1/τ} into q_absorb gives
    q_box = 4η/τ + q_absorb. This box bound is consumed by Phase 0 to ensure the
    parameter set fits within the ring theorem's working box. -/
def qBox (η τ : ℝ) : ℝ := 4 * η / τ + qAbsorb η

/-- Kaufman bad-direction constant loss: q_Kaufman = 2κ0 · q_box.

    The Kaufman projection energy bound carries a factor R^{2κ0} where R is the
    box radius from the quantitative box theorem. Since R ≤ δ^{-q_box}, we have
    R^{2κ0} ≤ δ^{-2κ0·q_box}, so the loss exponent is 2κ0·q_box. -/
def qKaufman (η τ κ0 : ℝ) : ℝ := 2 * κ0 * qBox η τ

/-- Normalized coordinate-energy loss: q_energy = 2κ0 · q_box.

    The normalized coordinate energy bound also carries an R^{2κ0} factor from
    the box radius, giving the same loss exponent as the Kaufman bound. -/
def qEnergy (η τ κ0 : ℝ) : ℝ := 2 * κ0 * qBox η τ

/-- Total graph density loss exponent: q_graph_total = q_init + q_G + 22·q_K + q_absorb.

    Combines:
    - q_init = 3ε+2η (initial product density)
    - q_G = 2·qProjective (M_G covering expansion)
    - qGraph = 22·q_K (BSG graph retention)
    - q_absorb (numerical constant absorption)

    This is the exponent in c_proj ≥ δ^{q_graph_total}. -/
def qGraphTotal (L η ε κ0 p_projective : ℝ) : ℝ :=
  qInit ε η + qG p_projective ε κ0 + qGraph L η ε κ0 p_projective + qAbsorb η

/-- Phase 0 plan regularity exponent: q_plan = 10η + q_absorb.

    From Phase 0 V2, C_Pbar = 4*(49C^4)/c^2 = 9604*C^8*δ^{-2η}.
    Since C ≤ δ^{-η}, C_Pbar ≤ 9604*δ^{-10η}. Absorbing the numerical
    constant 9604 into q_absorb gives q_plan = 10η + q_absorb. -/
def qPlan (η : ℝ) : ℝ := 10 * η + qAbsorb η

/-- Bad-direction threshold exponent: q_bad = q_plan + η + q_Kaufman + 2ε + q_absorb.

    Absorbs:
    - C_Pbar regularity (q_plan = 10η + q_absorb)
    - C_nu ~ C ≤ δ^{-η} (adds η)
    - Kaufman R^{2κ0} constant (q_Kaufman)
    - Leaves δ^{2ε} margin for bad-direction measure
    - Numerical constant absorption (q_absorb) -/
def qBad (η ε τ κ0 : ℝ) : ℝ :=
  qPlan η + η + qKaufman η τ κ0 + 2 * ε + qAbsorb η

/-- Total energy extraction loss exponent: η_energy = q_energy.

    Only the normalization cost; the full bad-direction threshold is qBad. -/
def etaEnergy (η τ κ0 : ℝ) : ℝ :=
  qEnergy η τ κ0

/-- Coordinate energy exponent: q_coord_energy = q_bad + 26ε. -/
def qCoordEnergy (η ε τ κ0 : ℝ) : ℝ :=
  qBad η ε τ κ0 + 26 * ε

/-- Normalized energy exponent: q_norm_energy = q_bad + 26ε + q_energy.

    This is the full energy loss that enters the terminal budget. -/
def qNormEnergy (η ε τ κ0 : ℝ) : ℝ :=
  qBad η ε τ κ0 + 26 * ε + qEnergy η τ κ0

/-- Total endgame loss exponent.

    qTotal = q_graph_total + 2·q_diff + qSizeLoss + η + ζ_dir + η_proj + q_norm_energy

    where qSizeLoss replaces the old qA and accounts for the actual N(B2)
    size loss after BSG retention: qSizeLoss = qEff + (L+3.5)η + qProjective.
    The extra η is the hP_small projection loss.

    q_norm_energy = q_bad + 26ε + q_energy accounts for the full
    energy extraction loss including C_Pbar regularity, Kaufman constant,
    and coordinate energy margin. -/
def qTotal (L η ε κ0 p_projective τ : ℝ) : ℝ :=
  qGraphTotal L η ε κ0 p_projective
  + 2 * qDiff L η ε κ0 p_projective
  + qSizeLoss L η ε κ0 p_projective
  + η
  + ζDir p_projective ε κ0
  + ηProj L η ε κ0 p_projective
  + qNormEnergy η ε τ κ0

/-! ## Non-negativity -/

lemma qProjective_nonneg {p_projective ε κ0 : ℝ}
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 ≤ qProjective p_projective ε κ0 := by
  dsimp only [qProjective]
  positivity

lemma qK_nonneg {L η ε κ0 p_projective : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η)
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 < qK L η ε κ0 p_projective := by
  dsimp only [qK]
  have h1 : 0 < (L + 2) * η := by positivity
  have h2 : 0 ≤ qProjective p_projective ε κ0 :=
    qProjective_nonneg hp_nonneg hε_nonneg hκ0_pos
  linarith

lemma qGraph_nonneg {L η ε κ0 p_projective : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η)
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 ≤ qGraph L η ε κ0 p_projective := by
  have hqK_pos : 0 < qK L η ε κ0 p_projective :=
    qK_nonneg hL_nonneg hη_pos hp_nonneg hε_nonneg hκ0_pos
  dsimp only [qGraph]
  exact mul_nonneg (by norm_num) hqK_pos.le

lemma qDiff_nonneg {L η ε κ0 p_projective : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η)
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 ≤ qDiff L η ε κ0 p_projective := by
  have hqK_pos : 0 < qK L η ε κ0 p_projective :=
    qK_nonneg hL_nonneg hη_pos hp_nonneg hε_nonneg hκ0_pos
  dsimp only [qDiff, qKA, qAbsorb]
  have h1 : 0 ≤ 80 * qK L η ε κ0 p_projective := by positivity
  have h2 : 0 ≤ 2 * (3 * η + η / 100) := by positivity
  have h3 : 0 ≤ η / 100 := by positivity
  linarith

lemma qBox_nonneg {η τ : ℝ} (hη_pos : 0 < η) (hτ_pos : 0 < τ) :
    0 ≤ qBox η τ := by
  dsimp only [qBox, qAbsorb]
  have h1 : 0 ≤ 4 * η / τ := by positivity
  have h2 : 0 ≤ η / 100 := by positivity
  linarith

lemma qA_nonneg {L η ε κ0 p_projective : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η)
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 ≤ qA L η ε κ0 p_projective := by
  have hqK_pos : 0 < qK L η ε κ0 p_projective :=
    qK_nonneg hL_nonneg hη_pos hp_nonneg hε_nonneg hκ0_pos
  dsimp only [qA]
  have h1 : 0 ≤ 10 * qK L η ε κ0 p_projective := by positivity
  have h2 : 0 ≤ 2 * η := by positivity
  linarith

lemma qSizeLoss_nonneg {L η ε κ0 p_projective : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η)
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 < qSizeLoss L η ε κ0 p_projective := by
  have hqK_pos : 0 < qK L η ε κ0 p_projective :=
    qK_nonneg hL_nonneg hη_pos hp_nonneg hε_nonneg hκ0_pos
  have hqP_nonneg : 0 ≤ qProjective p_projective ε κ0 :=
    qProjective_nonneg hp_nonneg hε_nonneg hκ0_pos
  dsimp only [qSizeLoss, qEff]
  have h1 : 0 < 10 * qK L η ε κ0 p_projective := by positivity
  have h21 : 0 ≤ L + (7 / 2 : ℝ) := by linarith
  have h2 : 0 ≤ (L + (7 / 2 : ℝ)) * η := by exact mul_nonneg h21 hη_pos.le
  have h3 : 0 ≤ qProjective p_projective ε κ0 := hqP_nonneg
  have h4 : 0 ≤ qAbsorb η := by dsimp only [qAbsorb] <;> positivity
  have h5 : 0 ≤ (L + (7 / 2 : ℝ)) * η + qProjective p_projective ε κ0 + qAbsorb η := by
    exact add_nonneg (add_nonneg h2 h3) h4
  have h6 : 0 < 10 * qK L η ε κ0 p_projective + ((L + (7 / 2 : ℝ)) * η + qProjective p_projective ε κ0 + qAbsorb η) :=
    add_pos_of_pos_of_nonneg h1 h5
  convert h6 using 1 <;> ring

lemma ζDir_nonneg {p_projective ε κ0 : ℝ}
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 ≤ ζDir p_projective ε κ0 :=
  qProjective_nonneg hp_nonneg hε_nonneg hκ0_pos

lemma qG_nonneg {p_projective ε κ0 : ℝ}
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 ≤ qG p_projective ε κ0 := by
  dsimp only [qG]
  have h1 : 0 ≤ qProjective p_projective ε κ0 :=
    qProjective_nonneg hp_nonneg hε_nonneg hκ0_pos
  linarith

lemma ηProj_nonneg {L η ε κ0 p_projective : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η)
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    0 ≤ ηProj L η ε κ0 p_projective := by
  have hqP : 0 ≤ qProjective p_projective ε κ0 :=
    qProjective_nonneg hp_nonneg hε_nonneg hκ0_pos
  dsimp only [ηProj]
  have h1 : 0 ≤ L * η := by positivity
  linarith

lemma qInit_nonneg {ε η : ℝ}
    (hε_nonneg : 0 ≤ ε) (hη_pos : 0 < η) :
    0 ≤ qInit ε η := by
  dsimp only [qInit]
  linarith

/-! ## Gap coefficient and feasibility -/

/-- Total loss coefficient: qTotal ≤ gapCoefficient · η.

    Accounts for all loss terms: qGraph, 2*qDiff, qSizeLoss + η, ζDir, ηProj,
    qNormEnergy (which includes qPlan, qKaufman, qEnergy, 26ε margin).

    The qSizeLoss term adds (L+2.5)η + qProjective beyond the old qA,
    increasing the coefficient by 2L+3 and one qProjective unit. -/
def gapCoefficient (L κ0 p_projective τ : ℝ) : ℝ :=
  192 * (L + 2) + 35 + 2 * L + 197 * p_projective / (10 * κ0)
  + 16 * κ0 / τ + κ0 / 25

lemma gapCoefficient_pos {L κ0 p_projective τ : ℝ}
    (hL_nonneg : 0 ≤ L) (hκ0_pos : 0 < κ0) (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ) :
    0 < gapCoefficient L κ0 p_projective τ := by
  dsimp only [gapCoefficient]
  have h1 : 0 < 192 * (L + 2) + 35 + 2 * L := by linarith
  have h2 : 0 ≤ 197 * p_projective / (10 * κ0) := by positivity
  have h3 : 0 < 16 * κ0 / τ + κ0 / 25 := by positivity
  linarith

/-- Total loss is bounded by gapCoefficient · η. -/
lemma qTotal_le_gapCoefficient_mul_η
    {L η ε κ0 p_projective τ : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η) (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0) (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (h10ε_lt_η : 10 * ε < η) :
    qTotal L η ε κ0 p_projective τ ≤ gapCoefficient L κ0 p_projective τ * η := by
  set qP : ℝ := qProjective p_projective ε κ0 with hqP_def
  set qKval : ℝ := qK L η ε κ0 p_projective with hqK_def
  have hqK_eq : qKval = (L + 2) * η + qP := by
    simp [hqK_def, hqP_def, qK, qProjective] <;> ring
  have h_eps_bound : qP ≤ p_projective * η / (10 * κ0) := by
    simp only [hqP_def, qProjective]
    have h4 : ε < η / 10 := by linarith
    have h5 : p_projective * ε ≤ p_projective * (η / 10) :=
      mul_le_mul_of_nonneg_left h4.le hp_nonneg
    have h6 : p_projective * ε / κ0 ≤ p_projective * (η / 10) / κ0 :=
      div_le_div_of_nonneg_right h5 (by positivity)
    have h7 : p_projective * (η / 10) / κ0 = p_projective * η / (10 * κ0) := by ring
    rw [h7] at h6; exact h6
  have h_main : qTotal L η ε κ0 p_projective τ =
      192 * qKval + (29.5 + 2 * L) * η + 5 * qP + 31 * ε + 10 * η / 100
      + 16 * κ0 / τ * η + κ0 / 25 * η := by
    simp [qTotal, qGraphTotal, qDiff, qKA, qAbsorb, qInit, qGraph, qG, qSizeLoss, qEff,
      ζDir, ηProj, qKaufman, qEnergy, qBox, qPlan, qBad, qNormEnergy, hqK_def, hqP_def] <;> ring
  have h31ε_lt_4η : 31 * ε < 4 * η := by
    have h : 10 * ε < η := h10ε_lt_η
    linarith
  have h10η100_lt_η : 10 * η / 100 < η := by linarith
  rw [h_main, hqK_eq]
  have h9 : 192 * ((L + 2) * η + qP) + (29.5 + 2 * L) * η + 5 * qP + 31 * ε + 10 * η / 100
        + 16 * κ0 / τ * η + κ0 / 25 * η ≤
      192 * ((L + 2) * η) + (35 + 2 * L) * η +
      197 * (p_projective * η / (10 * κ0))
      + 16 * κ0 / τ * η + κ0 / 25 * η := by
    have h10 : 192 * qP + 5 * qP ≤ 197 * (p_projective * η / (10 * κ0)) := by
      have h11 : 192 * qP + 5 * qP = 197 * qP := by ring
      rw [h11]
      gcongr <;> linarith
    have h12 : (29.5 + 2 * L) * η + 31 * ε + 10 * η / 100 ≤ (35 + 2 * L) * η := by
      have h13 : 31 * ε < 4 * η := h31ε_lt_4η
      have h14 : 10 * η / 100 < η := h10η100_lt_η
      linarith
    linarith
  have h12 : 192 * ((L + 2) * η) + (35 + 2 * L) * η +
        197 * (p_projective * η / (10 * κ0))
        + 16 * κ0 / τ * η + κ0 / 25 * η =
      gapCoefficient L κ0 p_projective τ * η := by
    simp [gapCoefficient] <;> ring
  calc
    192 * ((L + 2) * η + qP) + (29.5 + 2 * L) * η + 5 * qP + 31 * ε + 10 * η / 100
      + 16 * κ0 / τ * η + κ0 / 25 * η
      ≤ 192 * ((L + 2) * η) + (35 + 2 * L) * η +
          197 * (p_projective * η / (10 * κ0))
          + 16 * κ0 / τ * η + κ0 / 25 * η := h9
    _ = gapCoefficient L κ0 p_projective τ * η := h12

/-- **Budget feasibility theorem.**

If η < εgain / gapCoefficient, then εgain > qTotal.

This is the key result that allows the terminal budget inequality to hold.
All loss exponents are positive (never zero), and their sum is strictly
less than the Ring expansion exponent εgain. -/
theorem budget_feasible
    {εgain L η ε κ0 p_projective τ : ℝ}
    (hεgain_pos : 0 < εgain)
    (hL_nonneg : 0 ≤ L)
    (hη_pos : 0 < η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (h10ε_lt_η : 10 * ε < η)
    (h_small : η < εgain / gapCoefficient L κ0 p_projective τ) :
    εgain > qTotal L η ε κ0 p_projective τ := by
  set C : ℝ := gapCoefficient L κ0 p_projective τ with hC_def
  have hC_pos : 0 < C := gapCoefficient_pos hL_nonneg hκ0_pos hp_nonneg hτ_pos
  have h1 : qTotal L η ε κ0 p_projective τ ≤ C * η :=
    qTotal_le_gapCoefficient_mul_η hL_nonneg hη_pos hε_pos hκ0_pos hp_nonneg hτ_pos h10ε_lt_η
  have h2 : C * η < εgain := by
    have h3 : C * η < C * (εgain / C) :=
      mul_lt_mul_of_pos_left h_small hC_pos
    have h4 : C * (εgain / C) = εgain := by
      field_simp [hC_pos.ne'] <;> ring
    rw [h4] at h3; exact h3
  linarith

/-- **Existence of valid loss budget parameters.**

For any fixed L, κ0, s, τ, p_projective with κ0 > 0, κ0 < s, τ > 0,
and p_projective ≥ 10, there exist η > 0 and ε > 0 with 10ε < η such that
the budget holds, 5η < 2(s-κ0), and 4η < τ.

ε is chosen proportional to κ0·η/p_projective so that the Phase 3
density condition 3ε + qG + q_absorb ≤ η is satisfied.

η is chosen as min(εgain/(2C), (s-κ0)/3, τ/5) to satisfy the budget
gap, separation condition, and box popularity condition. -/
theorem exists_budget
    {εgain L κ0 s p_projective τ : ℝ}
    (hεgain_pos : 0 < εgain)
    (hL_nonneg : 0 ≤ L)
    (hκ0_pos : 0 < κ0)
    (hs_gt_κ0 : κ0 < s)
    (hp_ge_10 : 10 ≤ p_projective)
    (hτ_pos : 0 < τ) :
    ∃ (η ε : ℝ), 0 < η ∧ 0 < ε ∧ 10 * ε < η ∧
      5 * η < 2 * (s - κ0) ∧
      4 * η < τ ∧
      3 * ε + qG p_projective ε κ0 + qAbsorb η ≤ η ∧
      εgain > qTotal L η ε κ0 p_projective τ := by
  set C : ℝ := gapCoefficient L κ0 p_projective τ with hC_def
  have hC_pos : 0 < C := gapCoefficient_pos hL_nonneg hκ0_pos (by linarith) hτ_pos
  have hsκ0_pos : 0 < s - κ0 := by linarith
  set η1 : ℝ := εgain / (2 * C) with hη1_def
  set η2 : ℝ := (s - κ0) / 3 with hη2_def
  set η3 : ℝ := τ / 5 with hη3_def
  have hη1_pos : 0 < η1 := by positivity
  have hη2_pos : 0 < η2 := by positivity
  have hη3_pos : 0 < η3 := by positivity
  set η : ℝ := min η1 (min η2 η3) with hη_def
  have hη_pos : 0 < η := by
    exact lt_min hη1_pos (lt_min hη2_pos hη3_pos)
  have hη_le_η1 : η ≤ η1 := min_le_left _ _
  have hη_le_η2 : η ≤ min η2 η3 := min_le_right _ _
  have hη_le_η2' : η ≤ η2 := by
    exact le_trans hη_le_η2 (min_le_left _ _)
  have hη_le_η3 : η ≤ η3 := by
    exact le_trans hη_le_η2 (min_le_right _ _)
  set ε : ℝ := κ0 * η / (20 * p_projective + 10 * κ0) with hε_def
  have hε_pos : 0 < ε := by positivity
  have h10ε : 10 * ε < η := by
    rw [hε_def]
    have hpos : 0 < 20 * p_projective + 10 * κ0 := by linarith
    have h' : 10 * κ0 < 20 * p_projective + 10 * κ0 := by linarith
    have h : (10 * κ0) * η / (20 * p_projective + 10 * κ0) < η := by
      have h9 : (10 * κ0) * η / (20 * p_projective + 10 * κ0) <
          (20 * p_projective + 10 * κ0) * η / (20 * p_projective + 10 * κ0) := by
        gcongr <;> linarith
      have h10 : (20 * p_projective + 10 * κ0) * η / (20 * p_projective + 10 * κ0) = η := by
        field_simp [hpos.ne'] <;> ring
      rw [h10] at h9; exact h9
    have h'' : 10 * (κ0 * η / (20 * p_projective + 10 * κ0)) =
        (10 * κ0) * η / (20 * p_projective + 10 * κ0) := by ring
    rw [h'']; exact h
  have h5η : 5 * η < 2 * (s - κ0) := by
    have h : η ≤ (s - κ0) / 3 := hη_le_η2'
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
  have h_phase3 : 3 * ε + qG p_projective ε κ0 + qAbsorb η ≤ η := by
    simp only [hε_def, qG, qProjective, qAbsorb]
    have hpos : 0 < 20 * p_projective + 10 * κ0 := by linarith
    field_simp [hpos.ne', hκ0_pos.ne']
    <;> ring_nf <;> nlinarith
  have h_small : η < εgain / C := by
    have h1 : η ≤ εgain / (2 * C) := hη_le_η1
    have h2 : εgain / (2 * C) < εgain / C := by
      apply div_lt_div_of_pos_left hεgain_pos <;> linarith
    exact lt_of_le_of_lt h1 h2
  exact ⟨η, ε, hη_pos, hε_pos, h10ε, h5η, h4η, h_phase3,
    budget_feasible hεgain_pos hL_nonneg hη_pos hε_pos hκ0_pos (by linarith) hτ_pos h10ε h_small⟩

/-! ## Phase constant bound lemmas

These lemmas establish that the constants produced by each phase are bounded
by the appropriate power of δ.

### Proven lemmas
- `M_G_bound`: covering expansion factor from Lipschitz map
- `ring_constant_absorption`: general constant absorption

### Interface-defined lemmas (proofs deferred pending phase outputs)
- `K_A_bound`: requires Phase 3 mass capture
- `K_BSG_bound`: requires Phase 5-6 BSG + Ruzsa
- `projection_budget`: requires Phase 7 graph witness construction
-/

/-- **Phase 3 density condition**: The parameter choice
    ε = κ0·η / (20·p_projective + 10·κ0) ensures
    3ε + qG + q_absorb ≤ η.

    This is the condition needed for the product density lower bound to
    survive the M_G covering expansion and numerical constant absorption.

    Proof:
      3ε + qG + q_absorb
      = ε·(3 + 2·p_projective/κ0) + η/100
      = η·(3κ0 + 2p_projective)/(20p_projective + 10κ0) + η/100
      ≤ η·(3κ0 + 2p_projective)/(10·(2p_projective + κ0)) + η/100
      ≤ η·1/5 + η/100  [since (3κ0+2p)/(20p+10κ0) ≤ 1/5 for p,κ0 > 0]
      < η. -/
lemma phase3_density_condition
    {η ε κ0 p_projective : ℝ}
    (hη_pos : 0 < η)
    (hκ0_pos : 0 < κ0)
    (hp_pos : 0 < p_projective)
    (hε_def : ε = κ0 * η / (20 * p_projective + 10 * κ0)) :
    3 * ε + qG p_projective ε κ0 + qAbsorb η ≤ η := by
  simp only [hε_def, qG, qProjective, qAbsorb]
  have hpos : 0 < 20 * p_projective + 10 * κ0 := by linarith
  field_simp [hpos.ne', hκ0_pos.ne']
  <;> ring_nf <;> nlinarith

/-- **K_A bound** (interface): Comparability ratio exponent q_KA = 3η + q_absorb.

    Given upper bound U and lower bound L on the covering numbers N(A1), N(A2),
    bacon's `comparability_from_bounds` produces K_A := U / L satisfying
    two-sided comparability:
      N(A1) ≤ K_A · N(A2) and N(A2) ≤ K_A · N(A1).

    From Phase 3 energy-to-Frostman extraction:
      U ≤ δ^{-η} · M   (projection upper bound, M = sqrt(N(E)))
      L ≥ δ^{2η+q_absorb} · M   (mass capture lower bound; numerical
        constant (1/2)/C_triv/C2 absorbed into q_absorb = η/100)

    Therefore the comparability ratio satisfies:
      K_A = U / L ≤ δ^{-(3η+q_absorb)} = δ^{-q_KA}.

    This replaces the incorrect q_ratio = qProjective bound. -/
lemma K_A_bound
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {η U L M : ℝ}
    (hη_pos : 0 < η)
    (hM_pos : 0 < M)
    -- Actual bounds from Phase 3 extraction:
    (hU_le : U ≤ δ ^ (-η) * M)
    (hL_ge : L ≥ δ ^ (2 * η + qAbsorb η) * M)
    (hL_pos : 0 < L) :
    U / L ≤ δ ^ (-(3 * η + qAbsorb η)) := by
  have h1 : U / L ≤ (δ ^ (-η) * M) / L := by gcongr
  have h2 : (δ ^ (-η) * M) / L ≤ (δ ^ (-η) * M) / (δ ^ (2 * η + qAbsorb η) * M) := by
    gcongr <;> linarith
  have h3 : (δ ^ (-η) * M) / (δ ^ (2 * η + qAbsorb η) * M) = δ ^ (-η) / δ ^ (2 * η + qAbsorb η) := by
    field_simp [hM_pos.ne'] <;> ring
  have h4 : δ ^ (-η) / δ ^ (2 * η + qAbsorb η) = δ ^ (-(3 * η + qAbsorb η)) := by
    have h5 : δ ^ (-η) / δ ^ (2 * η + qAbsorb η) = δ ^ (-η - (2 * η + qAbsorb η)) := by
      rw [← Real.rpow_sub (by linarith)] <;> ring
    rw [h5] <;> ring_nf
  rw [h3, h4] at h2
  exact le_trans h1 h2

/-- **K_BSG bound** (interface): BSG difference constant exponent.

    Takes the actual K_BSG_all produced by Phase 5-6 (BSG + Ruzsa) and proves
    it is bounded by δ^{-(80·qK + 2·q_KA + q_absorb)}.

    The Phase56 output has the form:
      K_BSG_all ≤ C_numeric · δ^{-(80·qK + 2·q_KA)}

    where C_numeric is a fixed numerical constant and q_KA = 3η + q_absorb is the
    Phase 3 comparability ratio exponent. For δ sufficiently small,
    C_numeric ≤ δ^{-q_absorb}, so:
      K_BSG_all ≤ δ^{-(80·qK + 2·q_KA + q_absorb)}.

    This matches qDiff = 80·qK + 2·q_KA + q_absorb. -/
lemma K_BSG_bound
    {δ qK q_KA q_absorb : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hqK_nonneg : 0 ≤ qK) (hq_KA_nonneg : 0 ≤ q_KA)
    (hq_absorb_nonneg : 0 ≤ q_absorb)
    -- Actual K_BSG_all from Phase56:
    (K_BSG_all : ℝ) (hK_BSG_all_nonneg : 0 ≤ K_BSG_all)
    -- Numerical constant from Phase56:
    (C_numeric : ℝ) (hC_numeric_pos : 0 < C_numeric)
    -- Phase56 bound:
    (hK_BSG_le : K_BSG_all ≤ C_numeric * δ ^ (-(80 * qK + 2 * q_KA)))
    -- Constant absorption for δ small enough:
    (hC_absorb : C_numeric ≤ δ ^ (-q_absorb)) :
    K_BSG_all ≤ δ ^ (-(80 * qK + 2 * q_KA + q_absorb)) := by
  have h1 : K_BSG_all ≤ C_numeric * δ ^ (-(80 * qK + 2 * q_KA)) := hK_BSG_le
  have h2 : C_numeric * δ ^ (-(80 * qK + 2 * q_KA)) ≤
      δ ^ (-q_absorb) * δ ^ (-(80 * qK + 2 * q_KA)) := by
    gcongr
    <;> positivity
  have h3 : δ ^ (-q_absorb) * δ ^ (-(80 * qK + 2 * q_KA)) =
      δ ^ (-(80 * qK + 2 * q_KA + q_absorb)) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h3] at h2
  exact le_trans h1 h2

/-- **M_G bound** (proven): Covering expansion factor under Lipschitz map.

    If the inverse projective map has Lipschitz constant L_G ≤ δ^{-qProjective},
    then the covering number expansion factor is:
    M_G = (2·L_G·√2 + 6)^2 ≤ δ^{-2·qProjective}

    for δ sufficiently small (δ^{qProjective} ≤ 1/(2√2+6)). -/
lemma M_G_bound
    {δ qProjective : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hqP_nonneg : 0 ≤ qProjective)
    (hL_G : ∃ (L_G : ℝ), 0 ≤ L_G ∧ L_G ≤ δ ^ (-qProjective))
    (h_small_delta : δ ^ qProjective ≤ 1 / (2 * Real.sqrt 2 + 6)) :
    ∃ (M_G : ℝ), M_G ≤ (2 * Real.sqrt 2 + 6) ^ 2 * δ ^ (-2 * qProjective) := by
  rcases hL_G with ⟨L_G, hL_nonneg, hL_bound⟩
  let M_G : ℝ := (2 * L_G * Real.sqrt 2 + 6) ^ 2
  have hδ_inv_ge_one : 1 ≤ δ ^ (-qProjective) := by
    have h1 : 0 ≤ qProjective := hqP_nonneg
    have h2 : δ ^ qProjective ≤ 1 := by
      apply Real.rpow_le_one <;> linarith
    have h3 : 0 < δ ^ qProjective := by positivity
    have h4 : δ ^ (-qProjective) = (δ ^ qProjective)⁻¹ := by
      rw [Real.rpow_neg (by linarith)] <;> ring
    rw [h4]
    have h5 : (δ ^ qProjective)⁻¹ ≥ 1 := by
      have h51 : δ ^ qProjective ≤ 1 := h2
      have h52 : 0 < δ ^ qProjective := h3
      have h53 : (δ ^ qProjective)⁻¹ * δ ^ qProjective = 1 := by
        field_simp [h52.ne'] <;> ring
      nlinarith
    exact h5
  have h1 : 2 * L_G * Real.sqrt 2 + 6 ≤ (2 * Real.sqrt 2 + 6) * δ ^ (-qProjective) := by
    have h2 : 2 * L_G * Real.sqrt 2 ≤ 2 * Real.sqrt 2 * δ ^ (-qProjective) := by
      have h21 : L_G ≤ δ ^ (-qProjective) := hL_bound
      have h22 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      nlinarith
    have h3 : 6 ≤ 6 * δ ^ (-qProjective) := by
      have h4 : 1 ≤ δ ^ (-qProjective) := hδ_inv_ge_one
      nlinarith
    nlinarith
  have h4 : M_G ≤ ((2 * Real.sqrt 2 + 6) * δ ^ (-qProjective)) ^ 2 := by
    dsimp only [M_G]
    have h41 : 0 ≤ 2 * L_G * Real.sqrt 2 + 6 := by positivity
    have h42 : 0 ≤ (2 * Real.sqrt 2 + 6) * δ ^ (-qProjective) := by positivity
    gcongr
  have h5 : ((2 * Real.sqrt 2 + 6) * δ ^ (-qProjective)) ^ 2 =
      (2 * Real.sqrt 2 + 6) ^ 2 * (δ ^ (-qProjective)) ^ 2 := by ring
  have h6 : (δ ^ (-qProjective)) ^ 2 = δ ^ (-2 * qProjective) := by
    have h7 : (δ ^ (-qProjective)) ^ 2 = (δ ^ (-qProjective)) * (δ ^ (-qProjective)) := by ring
    rw [h7]
    have h8 : (δ ^ (-qProjective)) * (δ ^ (-qProjective)) = δ ^ (-qProjective + -qProjective) := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    rw [h8]
    have h9 : -qProjective + -qProjective = -2 * qProjective := by ring
    rw [h9]
  refine ⟨M_G, ?_⟩
  calc M_G
    ≤ ((2 * Real.sqrt 2 + 6) * δ ^ (-qProjective)) ^ 2 := h4
  _ = (2 * Real.sqrt 2 + 6) ^ 2 * (δ ^ (-qProjective)) ^ 2 := h5
  _ = (2 * Real.sqrt 2 + 6) ^ 2 * δ ^ (-2 * qProjective) := by rw [h6]

/-- **qA ≥ η**: the A-set enlargement exponent always absorbs the η loss
    from hP_small, since qA = 10·qK + 2·η ≥ η. -/
lemma qA_ge_eta {L η ε κ0 p_projective : ℝ}
    (hL_nonneg : 0 ≤ L) (hη_pos : 0 < η)
    (hp_nonneg : 0 ≤ p_projective) (hε_nonneg : 0 ≤ ε) (hκ0_pos : 0 < κ0) :
    qA L η ε κ0 p_projective ≥ η := by
  have hqK_pos : 0 < qK L η ε κ0 p_projective :=
    qK_nonneg hL_nonneg hη_pos hp_nonneg hε_nonneg hκ0_pos
  dsimp only [qA]
  linarith

/-- **Projection budget**: strict Phase 7 projection bound from the budget inequality.

    Given:
    - `h_transfer`: N(π_t(G_t)) < δ^{-(s+η+ζ_dir+η_proj)}  (from hP_small + FullLambda)
    - `hB2_lower`: N(B2) ≥ δ^{-s+qSizeLoss}  (actual BSG retention bound)
    - `hK_BSG_le`: K_BSG ≤ δ^{-q_diff}
    - `hc_proj_ge`: c_proj ≥ δ^{q_graph_total}
    - `h_budget`: εgain > q_graph_total + 2·q_diff + qSizeLoss + η + ζ_dir + η_proj
    - `h_delta_small`: δ^{gap} ≤ 1/32

    Then:
    N(π_t(G_t)) < (1/2)·(c_proj/(16·K_BSG²))·δ^{-εgain}·N(B2)

    This is the strict upper bound in the graph witness consumed by
    `sector_ring_lemma51_wrapper`.

    The caller must pass `q_graph_total = qInit + qG + qGraph + qAbsorb`,
    NOT just `qGraph = 22·qK`. The density constant c_proj carries the
    full density loss including initial product density and M_G expansion.

    ## Proof sketch

    Let `gap = εgain - (q_graph_total+2q_diff+qSizeLoss+η+ζ_dir+η_proj) > 0`.
    From the transfer bound:
    `N_proj < δ^{-(s+η+ζ+ηp)}`.

    Lower-bound the RHS:
    `RHS ≥ (1/32)·δ^{q_graph_total+2q_diff+qSizeLoss-εgain-s}`
    using `c_proj ≥ δ^{q_graph_total}`, `K_BSG ≤ δ^{-q_diff}`,
    `N(B2) ≥ δ^{-s+qSizeLoss}`.

    It suffices to show:
    `δ^{εgain-η-ζ-ηp} ≤ (1/32)·δ^{q_graph_total+2q_diff+qSizeLoss}`.

    Since `εgain-η-ζ-ηp = q_graph_total+2q_diff+qSizeLoss+gap`
    and `gap > 0`, `δ<1` gives:
    `δ^{εgain-η-ζ-ηp} = δ^{q_graph_total+2q_diff+qSizeLoss}·δ^{gap}
     ≤ (1/32)·δ^{q_graph_total+2q_diff+qSizeLoss}`.
-/
lemma projection_budget
    {δ s η εgain c_proj K_BSG : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hc_proj_pos : 0 < c_proj) (hK_BSG_pos : 0 < K_BSG)
    (hεgain_pos : 0 < εgain)
    {q_graph_total q_diff qSizeLoss ζ_dir η_proj : ℝ}
    (h_q_graph_total_nonneg : 0 ≤ q_graph_total)
    (h_q_diff_nonneg : 0 ≤ q_diff)
    (h_qSizeLoss_nonneg : 0 ≤ qSizeLoss)
    (hζ_dir_nonneg : 0 ≤ ζ_dir)
    (hη_proj_nonneg : 0 ≤ η_proj)
    (h_budget : εgain > q_graph_total + 2 * q_diff + qSizeLoss + η + ζ_dir + η_proj)
    {N_proj N_B2 : ENNReal}
    -- Phase 7 transfer: N(π_t(G_t)) < δ^{-(s+η+ζ_dir+η_proj)}
    -- (derived from hP_small: N(P)<δ^{-(2s+η)}, N(B1)≥δ^{-s}, chart Lipschitz δ^{-ζ_dir-η_proj})
    (h_transfer : N_proj < ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))))
    -- N(B2) lower bound (actual BSG retention: N(B2) ≥ const · δ^{-s+qSizeLoss})
    (hB2_lower : N_B2 ≥ ENNReal.ofReal (δ ^ (-s + qSizeLoss)))
    -- BSG constant and density constant bounds
    (hK_BSG_le : K_BSG ≤ δ ^ (-q_diff))
    (hc_proj_ge : c_proj ≥ δ ^ q_graph_total)
    -- δ small enough for numerical constant absorption
    (h_delta_small : δ ^ (εgain - (q_graph_total + 2 * q_diff + qSizeLoss + η + ζ_dir + η_proj)) ≤ 1 / 32)
    :
    N_proj < (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * N_B2 := by
  set gap : ℝ := εgain - (q_graph_total + 2 * q_diff + qSizeLoss + η + ζ_dir + η_proj) with hgap_def
  have hgap_pos : 0 < gap := by linarith [h_budget]
  have h_exponent_eq : εgain - η - ζ_dir - η_proj =
      q_graph_total + 2 * q_diff + qSizeLoss + gap := by
    simp [hgap_def] <;> ring
  have hδq_pos : 0 < δ ^ q_graph_total := by positivity
  have hδ_diff_pos : 0 < δ ^ (-q_diff) := by positivity
  have hK_BSG_sq_le : K_BSG ^ 2 ≤ (δ ^ (-q_diff)) ^ 2 := by gcongr
  have hδ2q_diff : (δ ^ (-q_diff)) ^ 2 = δ ^ (-2 * q_diff) := by
    have h1 : (δ ^ (-q_diff)) ^ 2 = δ ^ (-q_diff) * δ ^ (-q_diff) := by ring
    rw [h1, ← Real.rpow_add hδ_pos] <;> ring_nf
  have h_c_proj_lower : c_proj / (16 * K_BSG^2) ≥ (1 / 16 : ℝ) * δ ^ (q_graph_total + 2 * q_diff) := by
    have h1 : c_proj ≥ δ ^ q_graph_total := hc_proj_ge
    have h2 : K_BSG^2 ≤ δ ^ (-2 * q_diff) := by
      rw [hδ2q_diff] at hK_BSG_sq_le <;> exact hK_BSG_sq_le
    have h3 : c_proj / (16 * K_BSG^2) ≥ δ ^ q_graph_total / (16 * δ ^ (-2 * q_diff)) := by
      gcongr
      <;> linarith
    have h4 : δ ^ q_graph_total / (16 * δ ^ (-2 * q_diff)) =
        (1 / 16 : ℝ) * δ ^ (q_graph_total + 2 * q_diff) := by
      field_simp [hδ_pos.ne']
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h4] at h3
    exact h3
  have h_real3 : δ ^ (εgain - η - ζ_dir - η_proj) ≤
      (1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss) := by
    rw [h_exponent_eq]
    have h5 : δ ^ (q_graph_total + 2 * q_diff + qSizeLoss + gap) =
        δ ^ (q_graph_total + 2 * q_diff + qSizeLoss) * δ ^ gap := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    rw [h5]
    have h7 : δ ^ gap ≤ 1 / 32 := h_delta_small
    have h8 : 0 ≤ δ ^ (q_graph_total + 2 * q_diff + qSizeLoss) := by positivity
    nlinarith
  have h_real_upper : δ ^ (-(s + η + ζ_dir + η_proj)) ≤
      (1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s) := by
    have h9 : δ ^ (-(s + η + ζ_dir + η_proj)) =
        δ ^ (-s) * δ ^ (εgain - η - ζ_dir - η_proj) * δ ^ (-εgain) := by
      rw [← Real.rpow_add hδ_pos, ← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h9]
    have h10 : δ ^ (εgain - η - ζ_dir - η_proj) ≤ (1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss) := h_real3
    have h13 : δ ^ (-s) * δ ^ (εgain - η - ζ_dir - η_proj) * δ ^ (-εgain) ≤
        δ ^ (-s) * ((1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss)) * δ ^ (-εgain) := by
      gcongr
    have h14 : δ ^ (-s) * ((1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss)) * δ ^ (-εgain) =
        (1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s) := by
      have h15 : δ ^ (-s) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss) * δ ^ (-εgain) =
          δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s) := by
        rw [← Real.rpow_add hδ_pos, ← Real.rpow_add hδ_pos] <;> ring_nf
      linarith
    rw [h14] at h13
    exact h13
  have h_RHS_lower : (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
      ENNReal.ofReal (δ ^ (-εgain)) * N_B2 ≥
      ENNReal.ofReal ((1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s)) := by
    have h13 : (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * N_B2 ≥
        (1 / 2 : ENNReal) * ENNReal.ofReal ((1 / 16 : ℝ) * δ ^ (q_graph_total + 2 * q_diff)) *
        ENNReal.ofReal (δ ^ (-εgain)) * ENNReal.ofReal (δ ^ (-s + qSizeLoss)) := by
      gcongr
      <;> simpa using hB2_lower
    have h14 : (1 / 2 : ENNReal) * ENNReal.ofReal ((1 / 16 : ℝ) * δ ^ (q_graph_total + 2 * q_diff)) *
        ENNReal.ofReal (δ ^ (-εgain)) * ENNReal.ofReal (δ ^ (-s + qSizeLoss)) =
        ENNReal.ofReal ((1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s)) := by
      have h15 : (1 / 2 : ℝ) * ((1 / 16 : ℝ) * δ ^ (q_graph_total + 2 * q_diff)) * δ ^ (-εgain) * δ ^ (-s + qSizeLoss) =
          (1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s) := by
        have h16 : δ ^ (q_graph_total + 2 * q_diff) * δ ^ (-εgain) * δ ^ (-s + qSizeLoss) =
            δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s) := by
          have h16a : δ ^ (q_graph_total + 2 * q_diff) * δ ^ (-εgain) = δ ^ (q_graph_total + 2 * q_diff - εgain) :=
            (Real.rpow_add (by linarith) (q_graph_total + 2 * q_diff) (-εgain)).symm
          have h16b : δ ^ (q_graph_total + 2 * q_diff - εgain) * δ ^ (-s + qSizeLoss) = δ ^ (q_graph_total + 2 * q_diff - εgain + (-s + qSizeLoss)) :=
            (Real.rpow_add (by linarith) (q_graph_total + 2 * q_diff - εgain) (-s + qSizeLoss)).symm
          rw [h16a, h16b] <;> ring_nf
        linarith
      have h17 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
      rw [h17]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
      rw [h15]
    rw [h14] at h13
    exact h13
  have h_upper_le : ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) ≤
      ENNReal.ofReal ((1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s)) := by
    exact ENNReal.ofReal_le_ofReal h_real_upper
  calc N_proj
    < ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := h_transfer
  _ ≤ ENNReal.ofReal ((1 / 32 : ℝ) * δ ^ (q_graph_total + 2 * q_diff + qSizeLoss - εgain - s)) := h_upper_le
  _ ≤ (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * N_B2 := h_RHS_lower

/-- **Ring constant absorption** (proven): All phase constants can be
    absorbed into K_work · δ^{-εnc}.

    Given any finite collection of constants C_i and exponents q_i < εnc,
    if δ is small enough that C_i ≤ δ^{-(εnc - q_i)}, then
    C_i · δ^{-q_i} ≤ δ^{-εnc} ≤ K_work · δ^{-εnc} for K_work ≥ 1. -/
lemma ring_constant_absorption
    {δ εnc K_work : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hK_work_ge1 : 1 ≤ K_work)
    {C q : ℝ} (hq_lt_enc : q < εnc)
    (hC_absorb : C ≤ δ ^ (-(εnc - q))) :
    C * δ ^ (-q) ≤ K_work * δ ^ (-εnc) := by
  have h1 : C * δ ^ (-q) ≤ δ ^ (-(εnc - q)) * δ ^ (-q) := by
    gcongr
    <;> positivity
  have h2 : δ ^ (-(εnc - q)) * δ ^ (-q) = δ ^ (-εnc) := by
    have h3 : -(εnc - q) + (-q) = -εnc := by ring
    rw [← Real.rpow_add hδ_pos]
    <;> rw [h3]
  rw [h2] at h1
  have h4 : δ ^ (-εnc) ≤ K_work * δ ^ (-εnc) := by
    have h5 : 0 ≤ δ ^ (-εnc) := by positivity
    nlinarith
  exact le_trans h1 h4

/-! ## Terminal budget assembly

Given all phase outputs, assemble the terminal budget inequality
consumed by WirePhase9.
-/

/-- **M_G power absorption**: The numerical constant from `M_G_bound` can be
    absorbed into the qG exponent for sufficiently small δ.

    `M_G_bound` gives `M_G ≤ C_MG · δ^{-qG}` where `C_MG = (2√2+6)²` and
    `qG = 2·qProjective`. For any absorption margin `ε_absorb > 0`, if
    `δ^{ε_absorb} ≤ C_MG^{-1}`, then `C_MG ≤ δ^{-ε_absorb}` and hence:
    `M_G ≤ δ^{-(qG + ε_absorb)}`.

    This is used in the budget ledger to show that the M_G covering expansion
    is fully accounted for by the qG loss exponent (plus a negligible absorption
    margin that is swallowed by the Ring εgain gap). -/
lemma M_G_power_absorption
    {δ qG ε_absorb : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hqG_nonneg : 0 ≤ qG) (hε_absorb_pos : 0 < ε_absorb)
    (C_MG : ℝ) (hC_MG_pos : 0 < C_MG)
    (hM_G : ∃ (M_G : ℝ), 0 ≤ M_G ∧ M_G ≤ C_MG * δ ^ (-qG))
    (h_absorb : C_MG ≤ δ ^ (-ε_absorb)) :
    ∃ (M_G : ℝ), 0 ≤ M_G ∧ M_G ≤ δ ^ (-(qG + ε_absorb)) := by
  rcases hM_G with ⟨M_G, hM_G_nonneg, hM_G_le⟩
  refine ⟨M_G, hM_G_nonneg, ?_⟩
  have h1 : M_G ≤ C_MG * δ ^ (-qG) := hM_G_le
  have h2 : C_MG * δ ^ (-qG) ≤ δ ^ (-ε_absorb) * δ ^ (-qG) := by
    gcongr
    <;> positivity
  have h3 : δ ^ (-ε_absorb) * δ ^ (-qG) = δ ^ (-(qG + ε_absorb)) := by
    have h4 : δ ^ (-ε_absorb) * δ ^ (-qG) = δ ^ (-ε_absorb + -qG) :=
      (Real.rpow_add (by linarith) (-ε_absorb) (-qG)).symm
    rw [h4]
    have h5 : -ε_absorb + -qG = -(qG + ε_absorb) := by ring
    rw [h5]
  rw [h3] at h2
  exact le_trans h1 h2

/-- **Terminal budget lemma**: Produces the exact budget hypothesis
    required by `wire_phase9`.

    Takes all phase constant bounds and proves:
    εgain > q_graph_total + 2*q_diff + q_size_loss + η + ζ_dir + η_proj

    where:
    - q_graph_total = q_init + q_G + q_graph_total + q_absorb (total density loss)
    - q_diff = 3*q_eff + 2*q_ratio + q_absorb (safe difference bound)
    - q_size_loss = qEff + (L+3.5)η + qProjective (size loss from ideal δ^{-s})

    NOTE: q_size_loss + η replaces the old incorrect qA = 10·qK + 2η.
    ember verified q_size_loss + η > qA by (L+2.5)η + qProjective, so the old
    budget was insufficient.

    This is the main export of WireBudgets. -/
lemma terminal_budget
    {εgain L η ε κ0 p_projective τ : ℝ}
    (hεgain_pos : 0 < εgain)
    (hL_nonneg : 0 ≤ L)
    (hη_pos : 0 < η)
    (hε_pos : 0 < ε)
    (hκ0_pos : 0 < κ0)
    (hp_nonneg : 0 ≤ p_projective)
    (hτ_pos : 0 < τ)
    (h10ε_lt_η : 10 * ε < η)
    (h_small : η < εgain / gapCoefficient L κ0 p_projective τ) :
    let q_graph_total := qGraphTotal L η ε κ0 p_projective
    let q_diff := qDiff L η ε κ0 p_projective
    let q_size_loss := qSizeLoss L η ε κ0 p_projective
    let ζ_dir := ζDir p_projective ε κ0
    let η_proj := ηProj L η ε κ0 p_projective
    let q_norm_energy := qNormEnergy η ε τ κ0
    εgain > q_graph_total + 2 * q_diff + q_size_loss + η + ζ_dir + η_proj + q_norm_energy := by
  have h : εgain > qTotal L η ε κ0 p_projective τ :=
    budget_feasible hεgain_pos hL_nonneg hη_pos hε_pos hκ0_pos hp_nonneg hτ_pos
      h10ε_lt_η h_small
  simpa [qTotal, qNormEnergy] using h

/-! ## Generic numeric threshold helpers

Four reusable lemmas for the endgame skeleton's numeric conditions:

1. `constant_absorption_threshold`: C ≤ δ^{-q} for sufficiently small δ
2. `delta_rpow_antitone`: 0 < δ < 1 and a ≥ b implies δ^a ≤ δ^b
3. `absorbed_product_le`: C·δ^{-q1} ≤ δ^{-q2} when C is absorbed and exponents ordered
4. `absorbed_positive_power_le`: C·δ^{q1} ≤ δ^{q2} when C is absorbed and exponents ordered
-/

/-- **Constant absorption threshold**: for `C ≥ 1`, `q > 0`, there exists
    `d₀ > 0` such that `∀ 0 < δ ≤ d₀`, `C ≤ δ^{-q}`.
    Constructed as `d₀ = C^{-1/q}`. -/
lemma constant_absorption_threshold {C q : ℝ} (hC : 1 ≤ C) (hq : 0 < q) :
    ∃ (d₀ : ℝ), 0 < d₀ ∧ d₀ ≤ 1 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ d₀ → C ≤ δ ^ (-q) := by
  let d₀ : ℝ := C ^ (-1 / q)
  have hd₀_pos : 0 < d₀ := by positivity
  have hd₀_le_one : d₀ ≤ 1 := by
    dsimp only [d₀]
    have h1 : -1 / q ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hq.le
    have h2 : C ^ (-1 / q) ≤ C ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC h1
    have h3 : C ^ (0 : ℝ) = 1 := by simp
    exact h2.trans_eq h3
  have h_d0_q : d₀ ^ q = C⁻¹ := by
    dsimp only [d₀]
    have h6 : (C ^ (-1 / q)) ^ q = C ^ ((-1 / q) * q) := by
      rw [← Real.rpow_mul (by linarith)] <;> ring
    rw [h6]
    have h7 : (-1 / q) * q = -1 := by field_simp [hq.ne'] <;> ring
    rw [h7, Real.rpow_neg_one]
  refine ⟨d₀, hd₀_pos, hd₀_le_one, ?_⟩
  intro δ hδ_pos hδ_le
  have h3 : δ ^ q ≤ d₀ ^ q := by gcongr
  have h4 : δ ^ q ≤ C⁻¹ := by rw [h_d0_q] at h3; exact h3
  have h5 : 0 < δ ^ q := by positivity
  have h6 : C * δ ^ q ≤ 1 := by
    calc C * δ ^ q
        ≤ C * C⁻¹ := by gcongr
      _ = 1 := by field_simp [hC] <;> ring
  have h7 : C ≤ (δ ^ q)⁻¹ := by
    calc C
      = (C * δ ^ q) / (δ ^ q) := by field_simp [h5.ne'] <;> ring
    _ ≤ 1 / (δ ^ q) := by gcongr
    _ = (δ ^ q)⁻¹ := by ring
  have h8 : δ ^ (-q) = (δ ^ q)⁻¹ := by
    rw [Real.rpow_neg (by linarith)] <;> field_simp
  rw [h8]; exact h7

/-- **Exponent antitone**: for `0 < δ < 1`, if `a ≥ b` then `δ^a ≤ δ^b`. -/
lemma delta_rpow_antitone {δ a b : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h : a ≥ b) : δ ^ a ≤ δ ^ b :=
  Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h

/-- **Absorbed product bound**: if a constant `C` is absorbed into exponent
    `q_absorb` (i.e. `C ≤ δ^{-q_absorb}`), and `q_absorb + q1 ≤ q2`, then
    `C · δ^{-q1} ≤ δ^{-q2}`.

    This is the workhorse for conditions like `K0 · δ^{-6η} ≤ δ^{-Lη}`:
    choose `q_absorb` small enough that `q_absorb + 6η ≤ Lη`. -/
lemma absorbed_product_le {δ C q_absorb q1 q2 : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hC_absorb : C ≤ δ ^ (-q_absorb))
    (h_exponent_order : q_absorb + q1 ≤ q2)
    (hC_nonneg : 0 ≤ C) (hq1_nonneg : 0 ≤ q1) :
    C * δ ^ (-q1) ≤ δ ^ (-q2) := by
  have h1 : C * δ ^ (-q1) ≤ δ ^ (-q_absorb) * δ ^ (-q1) := by
    gcongr <;> exact hC_absorb
  have h2 : δ ^ (-q_absorb) * δ ^ (-q1) = δ ^ (-(q_absorb + q1)) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h2] at h1
  have h3 : -(q_absorb + q1) ≥ -q2 := by linarith
  have h4 : δ ^ (-(q_absorb + q1)) ≤ δ ^ (-q2) :=
    delta_rpow_antitone hδ_pos hδ_lt_one h3
  exact le_trans h1 h4

/-- **Absorbed positive-power bound**: if `C ≤ δ^{-q_absorb}` and
    `q1 - q_absorb ≥ q2`, then `C · δ^{q1} ≤ δ^{q2}`.

    This handles conditions like `C_energy · δ^{q_bad} ≤ δ^{2ε}`:
    since `q_bad` already contains a `2ε` margin plus positive terms,
    `q_bad - q_absorb ≥ 2ε` holds for small enough `q_absorb`. -/
lemma absorbed_positive_power_le {δ C q_absorb q1 q2 : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hC_absorb : C ≤ δ ^ (-q_absorb))
    (h_exponent_order : q1 - q_absorb ≥ q2)
    (hC_nonneg : 0 ≤ C) (hq1_nonneg : 0 ≤ q1) :
    C * δ ^ q1 ≤ δ ^ q2 := by
  have h1 : C * δ ^ q1 ≤ δ ^ (-q_absorb) * δ ^ q1 := by
    gcongr <;> exact hC_absorb
  have h2 : δ ^ (-q_absorb) * δ ^ q1 = δ ^ (q1 - q_absorb) := by
    rw [← Real.rpow_add hδ_pos] <;> ring_nf
  rw [h2] at h1
  have h4 : δ ^ (q1 - q_absorb) ≤ δ ^ q2 :=
    delta_rpow_antitone hδ_pos hδ_lt_one h_exponent_order
  exact le_trans h1 h4

end ProductLikeIncidence.ProductReduction
