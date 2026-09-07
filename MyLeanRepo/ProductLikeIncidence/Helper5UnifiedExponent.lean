module

/-
# Helper 5 Extension: Unified BSG Exponent Bound (FIXED)

Separate lemma that takes Helper5's existing outputs and constructs
`K_BSG_unified` with its exponent bound and domination facts.

**FIX (operator audit 8a46):** Removed radius-dependent `hδ_small` assumption.
The exponent bound now follows from `v4_normalized_exponent_absorption`,
which uses the V4 box budget `4*R ≤ δ^(-qBox)` instead of an ad-hoc
radius-dependent smallness condition.

## Key result

Given Helper5 outputs and V4 budget parameters, define:

    K_BSG_unified := 2 * R_ret * max K_BSG K_BSG_B2

Then:
- `0 < K_BSG_unified`
- `K_BSG_unified ≤ δ^(-qDiffV4)`
- Four domination facts for normalized bounds

## Dependencies
- `v4_normalized_exponent_absorption` from `NormalizedExponentAbsorption`
- Helper5 output `hR_ret_eq` (added in production 2025-08-11)

## Whiteprint node
Extension of `itr_bsg_extraction` for the H5→H6 bridge.
-/

public import MyLeanRepo.ProductLikeIncidence.NormalizedExponentAbsorption
public import MyLeanRepo.OSWPrelude

@[expose] public section

namespace ProductLikeIncidence.IncidenceToRingContradiction

open Real
open ProductLikeIncidence.ProductReduction (v4_normalized_exponent_absorption)

/-- Unified BSG exponent bound and domination facts (FIXED).

Uses V4 box budget absorption instead of radius-dependent smallness.

**Parameters:**
- V4 budget: qKV4, qKAV4, qGraphV4, qBox, qNormChunkV4, qDiffV4, η_work
- `R`: normalization radius (R_norm), with `4*R ≤ δ^(-qBox)`
- `R1`: R+1, with `2*R1+1 = 4*R+3`
- Helper5 outputs: K_BSG, K_BSG_B2, K_BSG_all, R_ret, hR_ret_eq
-/
lemma helper5_unified_exponent_v4
    {δ q_K qKA qAbsorb qDiffV3 : ℝ}
    {qKV4 qKAV4 qGraphV4 qBox qNormChunkV4 qDiffV4 η_work R R1 : ℝ}
    {K_BSG K_BSG_B2 K_BSG_all R_ret : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    -- V4 budget relationships
    (hqDiffV3_eq : qDiffV3 = 80 * q_K + 2 * qKA + qAbsorb)
    (hqKV4_ge : qKV4 ≥ q_K)
    (hqKAV4_ge : qKAV4 ≥ qKA)
    (hGraphV4_eq : qGraphV4 = 22 * qKV4 + η_work / 2 + η_work / 20)
    (hη_work_pos : 0 < η_work)
    (hqBox_nonneg : 0 ≤ qBox)
    (hNormChunk_eq : qNormChunkV4 = qGraphV4 + qBox + qAbsorb)
    (hDiffV4_eq : qDiffV4 = 80 * qKV4 + 2 * qKAV4 + qAbsorb + qNormChunkV4)
    -- Normalization radius bound (from upstream geometry)
    (h4R_le_qbox : 4 * R ≤ δ ^ (-qBox))
    (hR1_eq : 2 * R1 + 1 = 4 * R + 3)
    -- Helper5 outputs
    (hK_BSG_pos : 0 < K_BSG)
    (hK_BSG_B2_pos : 0 < K_BSG_B2)
    (hK_BSG_all_pos : 0 < K_BSG_all)
    (hK_BSG_le_all : K_BSG ≤ K_BSG_all)
    (hK_BSG_B2_le_all : K_BSG_B2 ≤ K_BSG_all)
    (hK_BSG_all_le : K_BSG_all ≤ δ ^ (-qDiffV3))
    (hR_ret_pos : 0 < R_ret)
    (hR_ret_eq : R_ret = 4 * (2 * R1 + 1) / (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))))
    -- Absorption threshold
    (h_absorb : δ ^ qAbsorb ≤ 1 / (512 * (3 ^ 22 : ℝ)))
    (hqAbsorb_pos : 0 < qAbsorb) :
    ∃ (K_BSG_unified : ℝ),
      K_BSG_unified = 2 * R_ret * max K_BSG K_BSG_B2 ∧
      0 < K_BSG_unified ∧
      K_BSG_unified ≤ δ ^ (-qDiffV4) ∧
      K_BSG * R_ret ≤ K_BSG_unified ∧
      2 * (K_BSG * R_ret) ≤ K_BSG_unified ∧
      K_BSG_B2 * R_ret ≤ K_BSG_unified ∧
      2 * (K_BSG_B2 * R_ret) ≤ K_BSG_unified := by
  set K_BSG_unified : ℝ := 2 * R_ret * max K_BSG K_BSG_B2 with hK_def

  -- Step 1: V4 absorption gives 2*R_ret*K_BSG_all ≤ δ^(-qDiffV4)
  have h_exp_bound : 2 * R_ret * K_BSG_all ≤ δ ^ (-qDiffV4) :=
    v4_normalized_exponent_absorption
      (hδ_pos := hδ_pos)
      (hδ_lt_one := hδ_lt_one)
      (hqDiffV3_eq := hqDiffV3_eq)
      (hqKV4_ge := hqKV4_ge)
      (hqKAV4_ge := hqKAV4_ge)
      (hGraphV4_eq := hGraphV4_eq)
      (hη_work_pos := hη_work_pos)
      (hqBox_nonneg := hqBox_nonneg)
      (hNormChunk_eq := hNormChunk_eq)
      (hDiffV4_eq := hDiffV4_eq)
      (h4R_le_qbox := h4R_le_qbox)
      (hR1_eq := hR1_eq)
      (hK_BSG_all_le := hK_BSG_all_le)
      (hK_BSG_all_pos := hK_BSG_all_pos)
      (hR_ret_eq := hR_ret_eq)
      (h_absorb := h_absorb)
      (hqAbsorb_pos := hqAbsorb_pos)

  -- Step 2: K_BSG_unified ≤ 2*R_ret*K_BSG_all
  have h1 : max K_BSG K_BSG_B2 ≤ K_BSG_all :=
    max_le hK_BSG_le_all hK_BSG_B2_le_all
  have h2 : 0 ≤ 2 * R_ret := by positivity
  have h3 : 2 * R_ret * max K_BSG K_BSG_B2 ≤ 2 * R_ret * K_BSG_all :=
    mul_le_mul_of_nonneg_left h1 h2

  have hK_BSG_unified_le : K_BSG_unified ≤ δ ^ (-qDiffV4) := by
    rw [hK_def]
    exact le_trans h3 h_exp_bound

  -- Step 3: Domination facts
  have h_dom1 : K_BSG * R_ret ≤ K_BSG_unified := by
    rw [hK_def]
    have h1 : K_BSG ≤ max K_BSG K_BSG_B2 := le_max_left _ _
    have h2 : K_BSG * R_ret ≤ (max K_BSG K_BSG_B2) * R_ret := by gcongr
    have h3 : (max K_BSG K_BSG_B2) * R_ret ≤ 2 * R_ret * (max K_BSG K_BSG_B2) := by
      have h4 : 0 ≤ R_ret * max K_BSG K_BSG_B2 := by positivity
      linarith
    exact le_trans h2 h3

  have h_dom2 : 2 * (K_BSG * R_ret) ≤ K_BSG_unified := by
    rw [hK_def]
    have h1 : K_BSG ≤ max K_BSG K_BSG_B2 := le_max_left _ _
    have h2 : 2 * (K_BSG * R_ret) ≤ 2 * ((max K_BSG K_BSG_B2) * R_ret) := by gcongr
    have h3 : 2 * ((max K_BSG K_BSG_B2) * R_ret) = 2 * R_ret * (max K_BSG K_BSG_B2) := by ring
    rw [h3] at h2; exact h2

  have h_dom3 : K_BSG_B2 * R_ret ≤ K_BSG_unified := by
    rw [hK_def]
    have h1 : K_BSG_B2 ≤ max K_BSG K_BSG_B2 := le_max_right _ _
    have h2 : K_BSG_B2 * R_ret ≤ (max K_BSG K_BSG_B2) * R_ret := by gcongr
    have h3 : (max K_BSG K_BSG_B2) * R_ret ≤ 2 * R_ret * (max K_BSG K_BSG_B2) := by
      have h4 : 0 ≤ R_ret * max K_BSG K_BSG_B2 := by positivity
      linarith
    exact le_trans h2 h3

  have h_dom4 : 2 * (K_BSG_B2 * R_ret) ≤ K_BSG_unified := by
    rw [hK_def]
    have h1 : K_BSG_B2 ≤ max K_BSG K_BSG_B2 := le_max_right _ _
    have h2 : 2 * (K_BSG_B2 * R_ret) ≤ 2 * ((max K_BSG K_BSG_B2) * R_ret) := by gcongr
    have h3 : 2 * ((max K_BSG K_BSG_B2) * R_ret) = 2 * R_ret * (max K_BSG K_BSG_B2) := by ring
    rw [h3] at h2; exact h2

  -- Positivity
  have h_pos : 0 < K_BSG_unified := by
    rw [hK_def]
    have h1 : 0 < max K_BSG K_BSG_B2 := by
      apply lt_max_of_lt_left
      exact hK_BSG_pos
    positivity

  exact ⟨K_BSG_unified, hK_def, h_pos, hK_BSG_unified_le,
    h_dom1, h_dom2, h_dom3, h_dom4⟩

end ProductLikeIncidence.IncidenceToRingContradiction
