module

/-
# Helper 5: BSG Extraction and Normalization

This module contains the standalone lemma `bsg_extraction_helper` corresponding
to the whiteprint node `itr_bsg_extraction`.

It takes the dense graph `Gamma` on `S1 × S2` (from Helper 4) and produces:
1. Raw subsets `B1 ⊆ S1`, `B2 ⊆ S2` with small sumset (via discretized BSG)
2. Raw dense graph `G'` on `B1 × B2`
3. Normalized subsets `B1_norm, B2_norm ⊆ productLikeUnitGrid δ`
4. Normalized dense graph `G_norm` and original `G_orig`
5. Size, density, and difference bounds for both raw and normalized sets

## Proof reference
Lines 2741-4029 of `.scratch/marlin/IncidenceToRingProof_v2.lean`.

## Dependencies
- `phase56_bsg_to_wrapper_inputs` — raw BSG extraction
- `normalize_chunk_grid_with_popularity` — unit-chunk normalization
- `delta_set_subset_with_retention` — normalized delta-set transfer
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeIncidence.Phase56Integration
public import MyLeanRepo.ProductLikeIncidence.NormalizeWithPopularity
public import MyLeanRepo.ProductLikeIncidence.NormalizationHelpers
public import MyLeanRepo.ProductLikeIncidence.NormalizedSetTransfer
public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.OSWPrelude

@[expose] public section

namespace ProductLikeIncidence.IncidenceToRingContradiction

open ProductLikeIncidence.ProductReduction
open Bornology

/-- Helper 5: BSG extraction and normalization.

Given dense graph `Gamma` on `S1 × S2` with `(δ, κ0)` regularity, extract
BSG subsets `B1, B2`, normalize to unit grid, and transfer all bounds. -/
lemma bsg_extraction_helper
    {δ s κ0 : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s)
    (hs_lt_one : s < 1)
    (hκ0_pos : 0 < κ0)
    (hκ0_lt_s : κ0 < s)
    -- Exponents
    {q_K θ_num q_input qSizeLossV3 qDiffV3 qKA qAbsorb : ℝ}
    (hq_K_pos : 0 < q_K)
    (hθ_num_pos : 0 < θ_num)
    (hqKA_nonneg : 0 ≤ qKA)
    (hqAbsorb_nonneg : 0 ≤ qAbsorb)
    (hq_input_nonneg : 0 ≤ q_input)
    (hqSizeLossV3_pos : 0 < qSizeLossV3)
    (hqDiffV3_eq : qDiffV3 = 80 * q_K + 2 * qKA + qAbsorb)
    (hqSizeLossV3_ge : q_input + 10 * q_K ≤ qSizeLossV3)
    -- Constants
    {C_A C_sum c_dense : ℝ}
    (hC_A_pos : 0 < C_A)
    (hC_sum_pos : 0 < C_sum)
    (hc_dense_pos : 0 < c_dense)
    (hC_sum_le : C_sum ≤ δ ^ (-q_K))
    (hc_dense_ge : c_dense ≥ δ ^ q_K)
    {K_A : ENNReal}
    (hK_A_ge_one : 1 ≤ K_A)
    (hK_A_ne_top : K_A ≠ ⊤)
    (hK_A_le : K_A ≤ ENNReal.ofReal (δ ^ (-qKA)))
    -- Absorption conditions
    (h_absorb_ret : δ ^ θ_num ≤ 1 / (3 ^ 10 : ℝ))
    (h_absorb_KBSG : (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 ≤ δ ^ (-qAbsorb))
    (h_absorb_size : δ ^ (qSizeLossV3 - q_input - 10 * q_K) ≤ 1 / (3 ^ 10 : ℝ))
    -- S1, S2
    {S1 S2 : Set ℝ}
    (hS1_le_S2 : Nreal δ S1 ≤ K_A * Nreal δ S2)
    (hS2_le_S1 : Nreal δ S2 ≤ K_A * Nreal δ S1)
    (hS1_lower : ENat.toENNReal S1.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    (hS2_lower : ENat.toENNReal S2.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    (hS1_delta : IsProductLikeRealDeltaSCSet δ κ0 C_A S1)
    (hS2_delta : IsProductLikeRealDeltaSCSet δ κ0 C_A S2)
    (hS1_nonempty : S1.Nonempty)
    (hS2_nonempty : S2.Nonempty)
    (hS1_fin : S1.Finite)
    (hS2_fin : S2.Finite)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    -- Gamma (dense graph)
    {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    (hGamma_sub : ∀ p ∈ Gamma, p 0 ∈ S1 ∧ p 1 ∈ S2)
    (hGamma_fin : Gamma.Finite)
    (hGamma_nonempty : Gamma.Nonempty)
    (hGamma_grid : ∀ p ∈ Gamma, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ))
    (hGamma_dense : ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
      ENNReal.ofReal c_dense * Nreal δ S1 * Nreal δ S2)
    (h_sumset : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      ENNReal.ofReal C_sum *
        ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)))
    -- Bounding radius for normalization
    {R_norm : ℝ}
    (hR_norm_pos : 0 < R_norm)
    (hR_norm_int : ∃ (c : ℤ), R_norm = (c : ℝ))
    (hS1_bdd : ∀ x ∈ S1, |x| ≤ R_norm + 1)
    (hS2_bdd : ∀ x ∈ S2, |x| ≤ R_norm + 1) :
    ∃ (B1 B2 : Set ℝ)
      (G' : Set (EuclideanSpace ℝ (Fin 2)))
      (C_BSG K_BSG K_BSG_B2 K_BSG_all : ℝ)
      (K_sector_B1 K_sector_B2 : ENNReal)
      (k j : ℤ)
      (B1_norm B2_norm : Set ℝ)
      (G_norm G_orig : Set (EuclideanSpace ℝ (Fin 2)))
      (R_ret M_ret : ℝ),
      -- ============================================================
      -- RAW OUTPUTS
      -- ============================================================
      B1 ⊆ S1 ∧
      B2 ⊆ S2 ∧
      G' ⊆ Gamma ∧
      (∀ p ∈ G', p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
      (∀ p ∈ G', ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
      G'.Nonempty ∧
      B1.Finite ∧ B2.Finite ∧
      B1.Nonempty ∧ B2.Nonempty ∧
      B1 ⊆ productLikeIntegerGrid δ ∧
      B2 ⊆ productLikeIntegerGrid δ ∧
      -- Raw delta-set at κ0 regularity
      IsProductLikeRealDeltaSCSet δ κ0 C_BSG B1 ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_BSG B2 ∧
      -- Raw size lower bounds (relative to S1/S2)
      ENat.toENNReal B1.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S1.encard ∧
      ENat.toENNReal B2.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S2.encard ∧
      -- Raw graph density
      ENat.toENNReal (dyadicCoveringNumber δ G') ≥
        ENNReal.ofReal (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) *
          Nreal δ B1 * Nreal δ B2 ∧
      -- Raw sector ledger (B1 normalization)
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B1 * Nreal δ B1 ∧
      -- Raw sector ledger (B2 normalization)
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B2 * Nreal δ B2 ∧
      -- Raw wrapper-ready real bounds (B1)
      0 < K_BSG ∧
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 ∧
      -- Raw wrapper-ready real bounds (B2)
      0 < K_BSG_B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      -- K_BSG_all domination and exponent facts
      0 < K_BSG_all ∧
      K_BSG ≤ K_BSG_all ∧
      K_BSG_B2 ≤ K_BSG_all ∧
      ENNReal.ofReal K_BSG_all ≥ K_sector_B1 ∧
      ENNReal.ofReal K_BSG_all ≥ K_sector_B2 ∧
      K_BSG_all ≤ δ ^ (-qDiffV3) ∧
      -- ============================================================
      -- NORMALIZED OUTPUTS
      -- ============================================================
      B1_norm ⊆ productLikeUnitGrid δ ∧
      B2_norm ⊆ productLikeUnitGrid δ ∧
      B1_norm.Nonempty ∧ B2_norm.Nonempty ∧
      B1_norm.Finite ∧ B2_norm.Finite ∧
      (∀ x ∈ B1_norm, ∀ y ∈ B1_norm, x ≠ y → |x - y| ≥ δ) ∧
      (∀ x ∈ B2_norm, ∀ y ∈ B2_norm, x ≠ y → |x - y| ≥ δ) ∧
      -- Normalized graph
      G_norm.Finite ∧
      (∀ p ∈ G_norm, ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ)) ∧
      (∀ p ∈ G_norm, p 0 ∈ B1_norm ∧ p 1 ∈ B2_norm) ∧
      G_orig ⊆ G' ∧
      (∀ p' ∈ G_norm, ∃ g ∈ G_orig, p' 0 = g 0 - (k : ℝ) ∧ p' 1 = g 1 - (j : ℝ)) ∧
      -- Normalized graph density
      (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4) *
        (B1_norm.ncard : ℝ) * (B2_norm.ncard : ℝ) ≤ (G_norm.ncard : ℝ) ∧
      -- Retention factors
      0 < R_ret ∧
      R_ret = 4 * (2 * (R_norm + 1) + 1) / (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) ∧
      0 < M_ret ∧
      C_BSG = C_A * δ ^ (-(10 * q_K + θ_num)) ∧
      M_ret = (2 * (R_norm + 1) + 1) * (3 ^ 10 : ℝ) / δ ^ (10 * q_K) ∧
      (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4) * (S1.ncard : ℝ) / M_ret ≤
        (B1_norm.ncard : ℝ) ∧
      (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) / 4) * (S2.ncard : ℝ) / M_ret ≤
        (B2_norm.ncard : ℝ) ∧
      -- Normalized size upper bounds
      Nreal δ B1_norm ≤ Nreal δ S1 ∧
      Nreal δ B2_norm ≤ Nreal δ S2 ∧
      -- Normalized delta-set (constant includes retention factor)
      IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B1_norm ∧
      IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B2_norm ∧
      -- Normalized difference bounds (B1 perspective, factor K_BSG * R_ret)
      Nreal δ (Set.image2 (· - ·) B1_norm B1_norm) ≤
        ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm ∧
      Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm ∧
      Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm ∧
      -- Normalized difference bounds (B2 perspective, factor K_BSG_B2 * R_ret)
      Nreal δ (Set.image2 (· - ·) B2_norm B2_norm) ≤
        ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm ∧
      Nreal δ (Set.image2 (· - ·) B1_norm B2_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm ∧
      Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
  -- =====================================================================
  -- Section 1: Raw BSG extraction via phase56_bsg_to_wrapper_inputs
  -- =====================================================================
  let C_BSG : ℝ := C_A * δ ^ (-(10 * q_K + θ_num))
  have hC_BSG_pos : 0 < C_BSG := by
    dsimp only [C_BSG]; have h1 : 0 < C_A := hC_A_pos; positivity
  rcases phase56_bsg_to_wrapper_inputs
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
      (hκ0_pos := hκ0_pos) (hκ0_lt_s := hκ0_lt_s)
      (hq_K_pos := hq_K_pos) (hθ_num_pos := hθ_num_pos)
      (hC_A_pos := hC_A_pos) (hC_sum_pos := hC_sum_pos)
      (hc_dense_pos := hc_dense_pos)
      (hqKA_nonneg := hqKA_nonneg) (hqAbsorb_nonneg := hqAbsorb_nonneg)
      (hq_input_nonneg := hq_input_nonneg)
      (hqSizeLossV3_pos := hqSizeLossV3_pos)
      (h_absorb_ret := h_absorb_ret)
      (h_absorb_KBSG := h_absorb_KBSG)
      (h_absorb_size := h_absorb_size)
      (hC_sum_le := hC_sum_le) (hc_dense_ge := hc_dense_ge)
      (hqDiffV3_eq := hqDiffV3_eq) (hqSizeLossV3_ge := hqSizeLossV3_ge)
      (K_A := K_A)
      (hS1_le_S2 := hS1_le_S2) (hS2_le_S1 := hS2_le_S1)
      (hK_A_ge_one := hK_A_ge_one) (hK_A_ne_top := hK_A_ne_top)
      (hK_A_le := hK_A_le)
      (hS1_lower := hS1_lower) (hS2_lower := hS2_lower)
      (hS1_delta := hS1_delta) (hS2_delta := hS2_delta)
      (hS1_nonempty := hS1_nonempty) (hS2_nonempty := hS2_nonempty)
      (hS1_fin := hS1_fin) (hS2_fin := hS2_fin)
      (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
      (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
      (hGamma_sub := hGamma_sub) (hGamma_fin := hGamma_fin)
      (hGamma_nonempty := hGamma_nonempty) (hGamma_grid := hGamma_grid)
      (hGamma_dense := hGamma_dense) (h_sumset := h_sumset)
    with ⟨B1, B2, G', K_BSG, K_BSG_B2, K_BSG_all, K_sector_B1, K_sector_B2,
      hB1_sub_S1, hB2_sub_S2, hG'_sub_Gamma, hG'_fibers, hG'_grid, hG'_nonempty,
      hB1_delta, hB2_delta,
      hB1_size_lower, hB2_size_lower,
      hB1_size_abs, hB2_size_abs,
      hG'_density,
      h_sec1_B1, h_sec2_B1, h_sec3_B1,
      h_sec1_B2, h_sec2_B2, h_sec3_B2,
      hK_BSG_pos, h_diff_self, h_diff_cross, h_sum_B1B2_B1,
      hK_BSG_B2_pos, h_diff_B2B2, h_diff_B2B1_B2, h_sum_B1B2_B2,
      hK_BSG_all_pos, hK_BSG_le_all, hK_BSG_B2_le_all,
      hK_BSG_all_B1, hK_BSG_all_B2, hK_BSG_all_le⟩

  -- =====================================================================
  -- Section 2: Derived B1/B2 properties
  -- =====================================================================
  have hB1_fin : B1.Finite := Set.Finite.subset hS1_fin hB1_sub_S1
  have hB2_fin : B2.Finite := Set.Finite.subset hS2_fin hB2_sub_S2
  have hB1_int_grid : B1 ⊆ productLikeIntegerGrid δ := subset_trans hB1_sub_S1 hS1_grid
  have hB2_int_grid : B2 ⊆ productLikeIntegerGrid δ := subset_trans hB2_sub_S2 hS2_grid
  have hB1_bdd_R1 : ∀ x ∈ B1, |x| ≤ R_norm + 1 := fun x hx => hS1_bdd x (hB1_sub_S1 hx)
  have hB2_bdd_R1 : ∀ x ∈ B2, |x| ≤ R_norm + 1 := fun x hx => hS2_bdd x (hB2_sub_S2 hx)
  have hB1_grid_ex : ∀ x ∈ B1, ∃ k : ℤ, x = δ * (k : ℝ) := by
    intro x hx
    have h : x ∈ productLikeIntegerGrid δ := hB1_int_grid hx
    simpa [productLikeIntegerGrid] using h
  have hB2_grid_ex : ∀ x ∈ B2, ∃ k : ℤ, x = δ * (k : ℝ) := by
    intro x hx
    have h : x ∈ productLikeIntegerGrid δ := hB2_int_grid hx
    simpa [productLikeIntegerGrid] using h
  have hG'_fin : G'.Finite := Set.Finite.subset hGamma_fin hG'_sub_Gamma
  have hB1_nonempty_bsg : B1.Nonempty := by
    rcases hG'_nonempty with ⟨p, hp⟩
    exact ⟨p 0, (hG'_fibers p hp).1⟩
  have hB2_nonempty_bsg : B2.Nonempty := by
    rcases hG'_nonempty with ⟨p, hp⟩
    exact ⟨p 1, (hG'_fibers p hp).2⟩

  -- =====================================================================
  -- Section 3: Density conversion to ncard form
  -- =====================================================================
  let c_bsg_real : ℝ := δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))
  have hc_bsg_real_pos : 0 < c_bsg_real := by positivity
  have hc_bsg_real_le_one : c_bsg_real ≤ 1 := by
    dsimp only [c_bsg_real]
    have h1 : δ ^ (22 * q_K) ≤ 1 := by
      have h2 : 0 ≤ 22 * q_K := by positivity
      have h3 : δ ^ (22 * q_K) ≤ δ ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h2
      simpa using h3
    have h4 : (16 * (3 ^ 22 : ℝ)) ≥ 1 := by norm_num
    calc δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))
      ≤ 1 / (16 * (3 ^ 22 : ℝ)) := by gcongr
    _ ≤ 1 := by norm_num

  -- Nreal = encard for grid-aligned finite sets (B1, B2)
  have hB1_line_grid : ∀ x ∈ productLikeRealLineCopy B1, ∀ i : Fin 1, ∃ k : ℤ, x i = δ * (k : ℝ) := by
    intro x hx i
    have h2 : x 0 ∈ B1 := hx
    have hi : i = 0 := Fin.eq_zero i
    rw [hi]
    exact hB1_grid_ex (x 0) h2
  have hB2_line_grid : ∀ x ∈ productLikeRealLineCopy B2, ∀ i : Fin 1, ∃ k : ℤ, x i = δ * (k : ℝ) := by
    intro x hx i
    have h2 : x 0 ∈ B2 := hx
    have hi : i = 0 := Fin.eq_zero i
    rw [hi]
    exact hB2_grid_ex (x 0) h2
  have h_line_copy_bij1 : (productLikeRealLineCopy B1).encard = B1.encard := by
    let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun x => (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
    have hf_inj : Function.Injective f := by
      intro x y h
      have h' : (f x) 0 = (f y) 0 := by rw [h]
      have hx : (f x) 0 = x := by simp [f]
      have hy : (f y) 0 = y := by simp [f]
      rw [hx, hy] at h'; exact h'
    have h_image : f '' B1 = productLikeRealLineCopy B1 := by
      ext z; simp only [Set.mem_image, productLikeRealLineCopy, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h5 : (f x) 0 = x := by simp [f]
        exact h5 ▸ hx
      · intro hz; refine ⟨z 0, hz, ?_⟩; ext i; have hi : i = 0 := Fin.eq_zero i; rw [hi]; simp [f]
    rw [← h_image]; exact hf_inj.encard_image B1
  have h_line_copy_bij2 : (productLikeRealLineCopy B2).encard = B2.encard := by
    let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun x => (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
    have hf_inj : Function.Injective f := by
      intro x y h
      have h' : (f x) 0 = (f y) 0 := by rw [h]
      have hx : (f x) 0 = x := by simp [f]
      have hy : (f y) 0 = y := by simp [f]
      rw [hx, hy] at h'; exact h'
    have h_image : f '' B2 = productLikeRealLineCopy B2 := by
      ext z; simp only [Set.mem_image, productLikeRealLineCopy, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h5 : (f x) 0 = x := by simp [f]
        exact h5 ▸ hx
      · intro hz; refine ⟨z 0, hz, ?_⟩; ext i; have hi : i = 0 := Fin.eq_zero i; rw [hi]; simp [f]
    rw [← h_image]; exact hf_inj.encard_image B2
  have h_nreal_B1 : Nreal δ B1 = ENat.toENNReal B1.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy B1) = (productLikeRealLineCopy B1).encard :=
      grid_set_coveringNumber_eq_encard hδ_pos hB1_line_grid
    have h2 : (productLikeRealLineCopy B1).encard = B1.encard := h_line_copy_bij1
    simpa [Nreal] using congr_arg ENat.toENNReal (h1.trans h2)
  have h_nreal_B2 : Nreal δ B2 = ENat.toENNReal B2.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy B2) = (productLikeRealLineCopy B2).encard :=
      grid_set_coveringNumber_eq_encard hδ_pos hB2_line_grid
    have h2 : (productLikeRealLineCopy B2).encard = B2.encard := h_line_copy_bij2
    simpa [Nreal] using congr_arg ENat.toENNReal (h1.trans h2)

  -- G' covering number = encard (grid-aligned in EuclideanSpace Fin 2)
  have h_cov_G' : dyadicCoveringNumber δ G' = G'.encard :=
    grid_set_coveringNumber_eq_encard hδ_pos hG'_grid

  -- Convert graph density to ncard form
  letI : Finite (↑B1 : Type _) := Set.finite_coe_iff.mpr hB1_fin
  letI : Finite (↑B2 : Type _) := Set.finite_coe_iff.mpr hB2_fin
  letI : Finite (↑G' : Type _) := Set.finite_coe_iff.mpr hG'_fin
  have h_encard_B1 : ENat.toENNReal B1.encard = ENNReal.ofReal (B1.ncard : ℝ) := by
    have h1 : B1.encard = ↑B1.ncard := (Set.coe_ncard_eq_encard B1).symm
    rw [h1]
    have h2 : ENat.toENNReal (↑B1.ncard : ENat) = (↑B1.ncard : ENNReal) := ENat.toENNReal_coe B1.ncard
    have h3 : ENNReal.ofReal (B1.ncard : ℝ) = (↑B1.ncard : ENNReal) := ENNReal.ofReal_natCast B1.ncard
    rw [h2, h3]
  have h_encard_B2 : ENat.toENNReal B2.encard = ENNReal.ofReal (B2.ncard : ℝ) := by
    have h1 : B2.encard = ↑B2.ncard := (Set.coe_ncard_eq_encard B2).symm
    rw [h1]
    have h2 : ENat.toENNReal (↑B2.ncard : ENat) = (↑B2.ncard : ENNReal) := ENat.toENNReal_coe B2.ncard
    have h3 : ENNReal.ofReal (B2.ncard : ℝ) = (↑B2.ncard : ENNReal) := ENNReal.ofReal_natCast B2.ncard
    rw [h2, h3]
  have h_encard_G' : ENat.toENNReal G'.encard = ENNReal.ofReal (G'.ncard : ℝ) := by
    have h1 : G'.encard = ↑G'.ncard := (Set.coe_ncard_eq_encard G').symm
    rw [h1]
    have h2 : ENat.toENNReal (↑G'.ncard : ENat) = (↑G'.ncard : ENNReal) := ENat.toENNReal_coe G'.ncard
    have h3 : ENNReal.ofReal (G'.ncard : ℝ) = (↑G'.ncard : ENNReal) := ENNReal.ofReal_natCast G'.ncard
    rw [h2, h3]
  have h_density_real : c_bsg_real * (B1.ncard : ℝ) * (B2.ncard : ℝ) ≤ (G'.ncard : ℝ) := by
    have h_density' : ENNReal.ofReal c_bsg_real * Nreal δ B1 * Nreal δ B2 ≤ ENat.toENNReal (dyadicCoveringNumber δ G') := hG'_density
    rw [h_nreal_B1, h_nreal_B2, h_cov_G', h_encard_B1, h_encard_B2, h_encard_G'] at h_density'
    have h4 : ENNReal.ofReal c_bsg_real * ENNReal.ofReal (B1.ncard : ℝ) * ENNReal.ofReal (B2.ncard : ℝ) =
        ENNReal.ofReal (c_bsg_real * (B1.ncard : ℝ) * (B2.ncard : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h4] at h_density'
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h_density'

  -- =====================================================================
  -- Section 4: Normalize via normalize_chunk_grid_with_popularity
  -- =====================================================================
  let R1 : ℝ := R_norm + 1
  have hR1_pos : 0 < R1 := by linarith [hR_norm_pos]
  have hR1_int : ∃ (c : ℤ), R1 = (c : ℝ) := by
    rcases hR_norm_int with ⟨c, hc⟩
    refine ⟨c + 1, ?_⟩
    have h : ((c + 1 : ℤ) : ℝ) = R_norm + 1 := by
      simp [hc] <;> linarith
    exact h.symm
  rcases normalize_chunk_grid_with_popularity
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic)
      (hR_pos := hR1_pos) (hR_int := hR1_int)
      (hS1_bdd := hB1_bdd_R1) (hS2_bdd := hB2_bdd_R1)
      (hS1_fin := hB1_fin) (hS2_fin := hB2_fin)
      (hGamma_sub := hG'_fibers)
      (hGamma_fin := hG'_fin)
      (hS1_grid := hB1_grid_ex) (hS2_grid := hB2_grid_ex)
      (hS1_nonempty := hB1_nonempty_bsg) (hS2_nonempty := hB2_nonempty_bsg)
      (c_dense := c_bsg_real) (hc_dense_pos := hc_bsg_real_pos) (hc_dense_le_one := hc_bsg_real_le_one)
      (h_density := h_density_real)
    with ⟨k, j, B1_norm, B2_norm, G_norm, G_orig,
      hB1_norm_unit, hB2_norm_unit,
      hB1_norm_nonempty, hB2_norm_nonempty,
      hG_norm_fin, hG_norm_grid, hG_norm_sub,
      hG_norm_density_ncard, hB1_retention_ncard, hB2_retention_ncard,
      hB1_eq, hB2_eq,
      hG_orig_sub, hG'_witness⟩

  -- =====================================================================
  -- Section 5: Normalized B1/B2 basic properties
  -- =====================================================================
  have hB1_norm_int_grid : B1_norm ⊆ productLikeIntegerGrid δ := by
    intro x hx; exact (hB1_norm_unit hx).1
  have hB2_norm_int_grid : B2_norm ⊆ productLikeIntegerGrid δ := by
    intro x hx; exact (hB2_norm_unit hx).1
  have hB1_norm_sub_Icc : B1_norm ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx; exact (hB1_norm_unit hx).2
  have hB2_norm_sub_Icc : B2_norm ⊆ Set.Icc (0 : ℝ) 1 := by
    intro x hx; exact (hB2_norm_unit hx).2
  have hB1_norm_fin : B1_norm.Finite := by
    rw [hB1_eq]
    exact Set.Finite.image _ (hB1_fin.subset (fun x hx => hx.1))
  have hB2_norm_fin : B2_norm.Finite := by
    rw [hB2_eq]
    exact Set.Finite.image _ (hB2_fin.subset (fun x hx => hx.1))
  have hB1_norm_sep : ∀ x ∈ B1_norm, ∀ y ∈ B1_norm, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hxy
    rw [hB1_eq] at hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    have h_ne : x' ≠ y' := by intro h; apply hxy; simp [h]
    have h_old : |x' - y'| ≥ δ := hS1_sep x' (hB1_sub_S1 hx'.1) y' (hB1_sub_S1 hy'.1) h_ne
    simpa using h_old
  have hB2_norm_sep : ∀ x ∈ B2_norm, ∀ y ∈ B2_norm, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hxy
    rw [hB2_eq] at hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    have h_ne : x' ≠ y' := by intro h; apply hxy; simp [h]
    have h_old : |x' - y'| ≥ δ := hS2_sep x' (hB2_sub_S2 hx'.1) y' (hB2_sub_S2 hy'.1) h_ne
    simpa using h_old

  -- =====================================================================
  -- Section 6: Retention factors and size bounds
  -- =====================================================================
  let M_ret : ℝ := (2 * R1 + 1) * (3 ^ 10 : ℝ) / δ ^ (10 * q_K)
  let R_ret : ℝ := 4 * (2 * R1 + 1) / c_bsg_real
  have hM_ret_pos : 0 < M_ret := by
    dsimp only [M_ret]
    have h1 : 0 < 2 * R1 + 1 := by linarith
    have h2 : 0 < δ ^ (10 * q_K) := by positivity
    positivity
  have hR_ret_pos : 0 < R_ret := by
    dsimp only [R_ret]
    have h1 : 0 < 2 * R1 + 1 := by linarith
    positivity
  have hR_ret_eq : R_ret = 4 * (2 * (R_norm + 1) + 1) / (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) := by
    dsimp only [R_ret, R1, c_bsg_real]
    <;> rfl

  -- S1/S2 encard to ncard
  letI : Finite (↑S1 : Type _) := Set.finite_coe_iff.mpr hS1_fin
  letI : Finite (↑S2 : Type _) := Set.finite_coe_iff.mpr hS2_fin
  have h_encard_S1 : ENat.toENNReal S1.encard = ENNReal.ofReal (S1.ncard : ℝ) := by
    have h1 : S1.encard = ↑S1.ncard := (Set.coe_ncard_eq_encard S1).symm
    rw [h1]
    have h2 : ENat.toENNReal (↑S1.ncard : ENat) = (↑S1.ncard : ENNReal) := ENat.toENNReal_coe S1.ncard
    have h3 : ENNReal.ofReal (S1.ncard : ℝ) = (↑S1.ncard : ENNReal) := ENNReal.ofReal_natCast S1.ncard
    rw [h2, h3]
  have h_encard_S2 : ENat.toENNReal S2.encard = ENNReal.ofReal (S2.ncard : ℝ) := by
    have h1 : S2.encard = ↑S2.ncard := (Set.coe_ncard_eq_encard S2).symm
    rw [h1]
    have h2 : ENat.toENNReal (↑S2.ncard : ENat) = (↑S2.ncard : ENNReal) := ENat.toENNReal_coe S2.ncard
    have h3 : ENNReal.ofReal (S2.ncard : ℝ) = (↑S2.ncard : ENNReal) := ENNReal.ofReal_natCast S2.ncard
    rw [h2, h3]

  -- Convert phase56 size lower bound to real form
  have hB1_size_real : (B1.ncard : ℝ) ≥ (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * (S1.ncard : ℝ) := by
    rw [h_encard_B1, h_encard_S1] at hB1_size_lower
    have h_mul : ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (S1.ncard : ℝ) =
        ENNReal.ofReal ((δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * (S1.ncard : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h_mul] at hB1_size_lower
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp hB1_size_lower
  have hB2_size_real : (B2.ncard : ℝ) ≥ (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * (S2.ncard : ℝ) := by
    rw [h_encard_B2, h_encard_S2] at hB2_size_lower
    have h_mul : ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (S2.ncard : ℝ) =
        ENNReal.ofReal ((δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * (S2.ncard : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h_mul] at hB2_size_lower
    exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mp hB2_size_lower

  -- Size lower bounds: (c_bsg_real/4) * S1.ncard / M_ret ≤ B1_norm.ncard
  have hB1_size_lower_norm : (c_bsg_real / 4) * (S1.ncard : ℝ) / M_ret ≤ (B1_norm.ncard : ℝ) := by
    dsimp only [M_ret]
    set factor := δ ^ (10 * q_K) / (3 ^ 10 : ℝ) with hfactor
    have h_factor_pos : 0 < factor := by positivity
    have h_R1_pos : 0 < (2 * R1 + 1 : ℝ) := by linarith
    have h_eq : (2 * R1 + 1 : ℝ) * (3 ^ 10 : ℝ) / δ ^ (10 * q_K) = (2 * R1 + 1 : ℝ) / factor := by
      field_simp [hfactor] <;> ring
    rw [h_eq]
    have h4 : (c_bsg_real / 4) * (S1.ncard : ℝ) / ((2 * R1 + 1 : ℝ) / factor) =
        (c_bsg_real / 4) * ((S1.ncard : ℝ) * factor) / (2 * R1 + 1 : ℝ) := by
      field_simp [h_R1_pos.ne', h_factor_pos.ne'] <;> ring
    rw [h4]
    have h5 : (S1.ncard : ℝ) * factor ≤ (B1.ncard : ℝ) := by
      have h6 : (B1.ncard : ℝ) ≥ factor * (S1.ncard : ℝ) := hB1_size_real
      linarith
    have h7 : (c_bsg_real / 4) * ((S1.ncard : ℝ) * factor) / (2 * R1 + 1 : ℝ) ≤
        (c_bsg_real / 4) * (B1.ncard : ℝ) / (2 * R1 + 1 : ℝ) := by
      gcongr
      <;> linarith
    exact le_trans h7 hB1_retention_ncard
  have hB2_size_lower_norm : (c_bsg_real / 4) * (S2.ncard : ℝ) / M_ret ≤ (B2_norm.ncard : ℝ) := by
    dsimp only [M_ret]
    set factor := δ ^ (10 * q_K) / (3 ^ 10 : ℝ) with hfactor
    have h_factor_pos : 0 < factor := by positivity
    have h_R1_pos : 0 < (2 * R1 + 1 : ℝ) := by linarith
    have h_eq : (2 * R1 + 1 : ℝ) * (3 ^ 10 : ℝ) / δ ^ (10 * q_K) = (2 * R1 + 1 : ℝ) / factor := by
      field_simp [hfactor] <;> ring
    rw [h_eq]
    have h4 : (c_bsg_real / 4) * (S2.ncard : ℝ) / ((2 * R1 + 1 : ℝ) / factor) =
        (c_bsg_real / 4) * ((S2.ncard : ℝ) * factor) / (2 * R1 + 1 : ℝ) := by
      field_simp [h_R1_pos.ne', h_factor_pos.ne'] <;> ring
    rw [h4]
    have h5 : (S2.ncard : ℝ) * factor ≤ (B2.ncard : ℝ) := by
      have h6 : (B2.ncard : ℝ) ≥ factor * (S2.ncard : ℝ) := hB2_size_real
      linarith
    have h7 : (c_bsg_real / 4) * ((S2.ncard : ℝ) * factor) / (2 * R1 + 1 : ℝ) ≤
        (c_bsg_real / 4) * (B2.ncard : ℝ) / (2 * R1 + 1 : ℝ) := by
      gcongr
      <;> linarith
    exact le_trans h7 hB2_retention_ncard

  -- Nreal = encard for normalized sets
  have hB1_norm_line_grid : ∀ x ∈ productLikeRealLineCopy B1_norm, ∀ i : Fin 1, ∃ m : ℤ, x i = δ * (m : ℝ) := by
    intro x hx i; have hi : i = 0 := Fin.eq_zero i; rw [hi]
    have h3 : x 0 ∈ productLikeIntegerGrid δ := hB1_norm_int_grid hx
    simpa [productLikeIntegerGrid] using h3
  have hB2_norm_line_grid : ∀ x ∈ productLikeRealLineCopy B2_norm, ∀ i : Fin 1, ∃ m : ℤ, x i = δ * (m : ℝ) := by
    intro x hx i; have hi : i = 0 := Fin.eq_zero i; rw [hi]
    have h3 : x 0 ∈ productLikeIntegerGrid δ := hB2_norm_int_grid hx
    simpa [productLikeIntegerGrid] using h3
  have h_nc_bij1 : (productLikeRealLineCopy B1_norm).encard = B1_norm.encard := by
    let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun x => (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
    have hf_inj : Function.Injective f := by
      intro x y h
      have h' : (f x) 0 = (f y) 0 := by rw [h]
      have hx : (f x) 0 = x := by simp [f]
      have hy : (f y) 0 = y := by simp [f]
      rw [hx, hy] at h'; exact h'
    have h_image : f '' B1_norm = productLikeRealLineCopy B1_norm := by
      ext z; simp only [Set.mem_image, productLikeRealLineCopy, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h5 : (f x) 0 = x := by simp [f]
        exact h5 ▸ hx
      · intro hz; refine ⟨z 0, hz, ?_⟩; ext i; have hi : i = 0 := Fin.eq_zero i; rw [hi]; simp [f]
    rw [← h_image]; exact hf_inj.encard_image B1_norm
  have h_nc_bij2 : (productLikeRealLineCopy B2_norm).encard = B2_norm.encard := by
    let f : ℝ → EuclideanSpace ℝ (Fin 1) := fun x => (WithLp.equiv 2 (Fin 1 → ℝ)).symm fun _ => x
    have hf_inj : Function.Injective f := by
      intro x y h
      have h' : (f x) 0 = (f y) 0 := by rw [h]
      have hx : (f x) 0 = x := by simp [f]
      have hy : (f y) 0 = y := by simp [f]
      rw [hx, hy] at h'; exact h'
    have h_image : f '' B2_norm = productLikeRealLineCopy B2_norm := by
      ext z; simp only [Set.mem_image, productLikeRealLineCopy, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h5 : (f x) 0 = x := by simp [f]
        exact h5 ▸ hx
      · intro hz; refine ⟨z 0, hz, ?_⟩; ext i; have hi : i = 0 := Fin.eq_zero i; rw [hi]; simp [f]
    rw [← h_image]; exact hf_inj.encard_image B2_norm
  letI : Finite (↑B1_norm : Type _) := Set.finite_coe_iff.mpr hB1_norm_fin
  letI : Finite (↑B2_norm : Type _) := Set.finite_coe_iff.mpr hB2_norm_fin
  have h_nreal_B1_norm : Nreal δ B1_norm = ENat.toENNReal B1_norm.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy B1_norm) = (productLikeRealLineCopy B1_norm).encard :=
      grid_set_coveringNumber_eq_encard hδ_pos hB1_norm_line_grid
    have h2 : (productLikeRealLineCopy B1_norm).encard = B1_norm.encard := h_nc_bij1
    simpa [Nreal] using congr_arg ENat.toENNReal (h1.trans h2)
  have h_nreal_B2_norm : Nreal δ B2_norm = ENat.toENNReal B2_norm.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy B2_norm) = (productLikeRealLineCopy B2_norm).encard :=
      grid_set_coveringNumber_eq_encard hδ_pos hB2_norm_line_grid
    have h2 : (productLikeRealLineCopy B2_norm).encard = B2_norm.encard := h_nc_bij2
    simpa [Nreal] using congr_arg ENat.toENNReal (h1.trans h2)
  have h_encard_B1_norm : ENat.toENNReal B1_norm.encard = ENNReal.ofReal (B1_norm.ncard : ℝ) := by
    have h1 : B1_norm.encard = ↑B1_norm.ncard := (Set.coe_ncard_eq_encard B1_norm).symm
    rw [h1]; have h2 := ENat.toENNReal_coe B1_norm.ncard
    have h3 := ENNReal.ofReal_natCast B1_norm.ncard; rw [h2, h3]
  have h_encard_B2_norm : ENat.toENNReal B2_norm.encard = ENNReal.ofReal (B2_norm.ncard : ℝ) := by
    have h1 : B2_norm.encard = ↑B2_norm.ncard := (Set.coe_ncard_eq_encard B2_norm).symm
    rw [h1]; have h2 := ENat.toENNReal_coe B2_norm.ncard
    have h3 := ENNReal.ofReal_natCast B2_norm.ncard; rw [h2, h3]

  -- Retention: B1.ncard ≤ R_ret * B1_norm.ncard
  have h_ret_B1_real : (B1.ncard : ℝ) ≤ R_ret * (B1_norm.ncard : ℝ) := by
    dsimp only [R_ret]
    set a := c_bsg_real / 4 with ha
    set b := (2 * R1 + 1 : ℝ) with hb
    have ha_pos : 0 < a := by positivity
    have hb_pos : 0 < b := by linarith
    have h_ne1 : a ≠ 0 := ha_pos.ne'
    have h_ne2 : b ≠ 0 := hb_pos.ne'
    have h : a * (B1.ncard : ℝ) / b ≤ (B1_norm.ncard : ℝ) := hB1_retention_ncard
    have h' : a * (B1.ncard : ℝ) ≤ b * (B1_norm.ncard : ℝ) := by
      have h9 : a * (B1.ncard : ℝ) = b * (a * (B1.ncard : ℝ) / b) := by field_simp [h_ne2] <;> ring
      rw [h9]; exact mul_le_mul_of_nonneg_left h (by linarith)
    have h10 : (B1.ncard : ℝ) ≤ (b / a) * (B1_norm.ncard : ℝ) := by
      calc (B1.ncard : ℝ)
        = (1 / a) * (a * (B1.ncard : ℝ)) := by field_simp [h_ne1] <;> ring
      _ ≤ (1 / a) * (b * (B1_norm.ncard : ℝ)) := by gcongr
      _ = (b / a) * (B1_norm.ncard : ℝ) := by field_simp [h_ne1] <;> ring
    have h_eq : b / a = R_ret := by dsimp only [R_ret, a, b]; field_simp [h_ne1] <;> ring
    rw [h_eq] at h10; exact h10
  have h_ret_B2_real : (B2.ncard : ℝ) ≤ R_ret * (B2_norm.ncard : ℝ) := by
    dsimp only [R_ret]
    set a := c_bsg_real / 4 with ha
    set b := (2 * R1 + 1 : ℝ) with hb
    have ha_pos : 0 < a := by positivity
    have hb_pos : 0 < b := by linarith
    have h_ne1 : a ≠ 0 := ha_pos.ne'
    have h_ne2 : b ≠ 0 := hb_pos.ne'
    have h : a * (B2.ncard : ℝ) / b ≤ (B2_norm.ncard : ℝ) := hB2_retention_ncard
    have h' : a * (B2.ncard : ℝ) ≤ b * (B2_norm.ncard : ℝ) := by
      have h9 : a * (B2.ncard : ℝ) = b * (a * (B2.ncard : ℝ) / b) := by field_simp [h_ne2] <;> ring
      rw [h9]; exact mul_le_mul_of_nonneg_left h (by linarith)
    have h10 : (B2.ncard : ℝ) ≤ (b / a) * (B2_norm.ncard : ℝ) := by
      calc (B2.ncard : ℝ)
        = (1 / a) * (a * (B2.ncard : ℝ)) := by field_simp [h_ne1] <;> ring
      _ ≤ (1 / a) * (b * (B2_norm.ncard : ℝ)) := mul_le_mul_of_nonneg_left h' (by positivity)
      _ = (b / a) * (B2_norm.ncard : ℝ) := by field_simp [h_ne1] <;> ring
    have h_eq : b / a = R_ret := by dsimp only [R_ret, a, b]; field_simp [h_ne1] <;> ring
    rw [h_eq] at h10; exact h10

  -- ENNReal retention bounds
  have h_retention_B1 : Nreal δ B1 ≤ ENNReal.ofReal R_ret * Nreal δ B1_norm := by
    rw [h_nreal_B1, h_nreal_B1_norm, h_encard_B1, h_encard_B1_norm]
    have h5 : ENNReal.ofReal (B1.ncard : ℝ) ≤ ENNReal.ofReal (R_ret * (B1_norm.ncard : ℝ)) := by
      exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h_ret_B1_real
    rw [ENNReal.ofReal_mul (by positivity)] at h5; exact h5
  have h_retention_B2 : Nreal δ B2 ≤ ENNReal.ofReal R_ret * Nreal δ B2_norm := by
    rw [h_nreal_B2, h_nreal_B2_norm, h_encard_B2, h_encard_B2_norm]
    have h5 : ENNReal.ofReal (B2.ncard : ℝ) ≤ ENNReal.ofReal (R_ret * (B2_norm.ncard : ℝ)) := by
      exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h_ret_B2_real
    rw [ENNReal.ofReal_mul (by positivity)] at h5; exact h5

  -- =====================================================================
  -- Section 7: Chunk subset relations
  -- =====================================================================
  have h_chunk1 : (fun x : ℝ => x + (k : ℝ)) '' B1_norm ⊆ B1 := by
    intro z hz
    rcases hz with ⟨w, hw, hz_eq⟩
    have h5 : w ∈ Set.image (fun x : ℝ => x - (k : ℝ)) (unitChunk B1 k) :=
      hB1_eq ▸ hw
    rcases h5 with ⟨x, hx, hwx⟩
    have h_z_eq_x : z = x := by
      calc z
        = w + (k : ℝ) := hz_eq.symm
      _ = (x - (k : ℝ)) + (k : ℝ) := by rw [hwx.symm]
      _ = x := by ring
    rw [h_z_eq_x]
    exact hx.1
  have h_chunk2 : (fun x : ℝ => x + (j : ℝ)) '' B2_norm ⊆ B2 := by
    intro z hz
    rcases hz with ⟨w, hw, hz_eq⟩
    have h5 : w ∈ Set.image (fun x : ℝ => x - (j : ℝ)) (unitChunk B2 j) :=
      hB2_eq ▸ hw
    rcases h5 with ⟨x, hx, hwx⟩
    have h_z_eq_x : z = x := by
      calc z
        = w + (j : ℝ) := hz_eq.symm
      _ = (x - (j : ℝ)) + (j : ℝ) := by rw [hwx.symm]
      _ = x := by ring
    rw [h_z_eq_x]
    exact hx.1

  -- =====================================================================
  -- Section 8: Normalized δ-set transfer
  -- =====================================================================
  have hκ0_le_one : κ0 ≤ 1 := by linarith [hκ0_lt_s, hs_lt_one]
  have hB1_norm_bdd : Bornology.IsBounded B1_norm :=
    Bornology.IsBounded.subset (Metric.isBounded_Icc _ _) hB1_norm_sub_Icc
  have hB2_norm_bdd : Bornology.IsBounded B2_norm :=
    Bornology.IsBounded.subset (Metric.isBounded_Icc _ _) hB2_norm_sub_Icc

  let B1_minus_k := ProductReduction.translateSet (-(k : ℝ)) B1
  let B2_minus_j := ProductReduction.translateSet (-(j : ℝ)) B2

  have hB1_minus_k_delta : IsProductLikeRealDeltaSCSet δ κ0 C_BSG B1_minus_k := by
    simpa [C_BSG, B1_minus_k] using
      isProductLikeRealDeltaSCSet_translate_by_int (-k) hδ_dyadic hδ_pos hB1_delta
  have hB2_minus_j_delta : IsProductLikeRealDeltaSCSet δ κ0 C_BSG B2_minus_j := by
    simpa [C_BSG, B2_minus_j] using
      isProductLikeRealDeltaSCSet_translate_by_int (-j) hδ_dyadic hδ_pos hB2_delta

  have hB1_norm_sub_minus : B1_norm ⊆ B1_minus_k := by
    intro y hy
    have h1 : y + (k : ℝ) ∈ B1 := h_chunk1 ⟨y, hy, by ring⟩
    exact ⟨y + (k : ℝ), h1, by ring⟩
  have hB2_norm_sub_minus : B2_norm ⊆ B2_minus_j := by
    intro y hy
    have h1 : y + (j : ℝ) ∈ B2 := h_chunk2 ⟨y, hy, by ring⟩
    exact ⟨y + (j : ℝ), h1, by ring⟩

  have hN_B1_minus_k : Nreal δ B1_minus_k = Nreal δ B1 := by
    simpa [B1_minus_k] using nreal_translate_by_int hδ_dyadic hB1_fin.isBounded (-k)
  have hN_B2_minus_j : Nreal δ B2_minus_j = Nreal δ B2 := by
    simpa [B2_minus_j] using nreal_translate_by_int hδ_dyadic hB2_fin.isBounded (-j)

  have h_retention_minus1 : Nreal δ B1_minus_k ≤ ENNReal.ofReal R_ret * Nreal δ B1_norm := by
    rw [hN_B1_minus_k]; exact h_retention_B1
  have h_retention_minus2 : Nreal δ B2_minus_j ≤ ENNReal.ofReal R_ret * Nreal δ B2_norm := by
    rw [hN_B2_minus_j]; exact h_retention_B2

  have hB1_norm_delta : IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B1_norm :=
    delta_set_subset_with_retention
      hB1_norm_bdd hB1_norm_nonempty
      hδ_pos hδ_dyadic
      (by linarith [hκ0_pos]) hκ0_le_one
      hC_BSG_pos hR_ret_pos
      hB1_minus_k_delta hB1_norm_sub_minus h_retention_minus1
  have hB2_norm_delta : IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B2_norm :=
    delta_set_subset_with_retention
      hB2_norm_bdd hB2_norm_nonempty
      hδ_pos hδ_dyadic
      (by linarith [hκ0_pos]) hκ0_le_one
      hC_BSG_pos hR_ret_pos
      hB2_minus_j_delta hB2_norm_sub_minus h_retention_minus2
  -- =====================================================================
  -- Section 9: Size upper bounds
  -- =====================================================================
  have hB1_norm_size_upper : Nreal δ B1_norm ≤ Nreal δ S1 := by
    have h2 : Nreal δ B1_norm ≤ Nreal δ B1_minus_k := Nreal_mono hB1_norm_sub_minus
    rw [hN_B1_minus_k] at h2
    have h3 : Nreal δ B1 ≤ Nreal δ S1 := Nreal_mono hB1_sub_S1
    exact le_trans h2 h3
  have hB2_norm_size_upper : Nreal δ B2_norm ≤ Nreal δ S2 := by
    have h2 : Nreal δ B2_norm ≤ Nreal δ B2_minus_j := Nreal_mono hB2_norm_sub_minus
    rw [hN_B2_minus_j] at h2
    have h3 : Nreal δ B2 ≤ Nreal δ S2 := Nreal_mono hB2_sub_S2
    exact le_trans h2 h3

  -- =====================================================================
  -- Section 10: Normalized difference/sum bounds (6 bounds)
  -- =====================================================================
  have hB1B1_bdd : Bornology.IsBounded (Set.image2 (· - ·) B1 B1) :=
    (Set.Finite.image2 (· - ·) hB1_fin hB1_fin).isBounded
  have hB2B1_bdd : Bornology.IsBounded (Set.image2 (· - ·) B2 B1) :=
    (Set.Finite.image2 (· - ·) hB2_fin hB1_fin).isBounded
  have hB1B2_sum_bdd : Bornology.IsBounded (Set.image2 (· + ·) B1 B2) :=
    (Set.Finite.image2 (· + ·) hB1_fin hB2_fin).isBounded
  have hB2B2_bdd : Bornology.IsBounded (Set.image2 (· - ·) B2 B2) :=
    (Set.Finite.image2 (· - ·) hB2_fin hB2_fin).isBounded
  have hB1B2_diff_bdd : Bornology.IsBounded (Set.image2 (· - ·) B1 B2) :=
    (Set.Finite.image2 (· - ·) hB1_fin hB2_fin).isBounded

  have hB2B1_grid : (Set.image2 (· - ·) B2 B1) ⊆ productLikeIntegerGrid δ := by
    intro z hz
    rcases Set.mem_image2.mp hz with ⟨x, hx, y, hy, rfl⟩
    rcases hB2_grid_ex x hx with ⟨kx, hkx⟩
    rcases hB1_grid_ex y hy with ⟨ky, hky⟩
    rw [hkx, hky]
    refine ⟨kx - ky, by simp [mul_sub] <;> ring⟩

  have hKR1 : ENNReal.ofReal K_BSG * ENNReal.ofReal R_ret = ENNReal.ofReal (K_BSG * R_ret) :=
    (ENNReal.ofReal_mul (show 0 ≤ K_BSG from by linarith)).symm
  have hKR2 : ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret = ENNReal.ofReal (K_BSG_B2 * R_ret) :=
    (ENNReal.ofReal_mul (show 0 ≤ K_BSG_B2 from by linarith)).symm

  -- Bound 1: B1 self-diff (B1 perspective)
  have h_norm1 : Nreal δ (Set.image2 (· - ·) B1_norm B1_norm) ≤
      ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm := by
    have h := normalized_self_difference_transfer h_diff_self h_retention_B1 h_chunk1
    calc _ ≤ ENNReal.ofReal K_BSG * ENNReal.ofReal R_ret * Nreal δ B1_norm := h
         _ = ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm := by
           exact congr_arg (fun x => x * Nreal δ B1_norm) hKR1

  -- Bound 2: B2-B1 cross-diff (B1 perspective)
  have h_norm2 : Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm := by
    have h := normalized_cross_difference_transfer
      hδ_pos hB2B1_bdd h_diff_cross h_retention_B1 h_chunk1 h_chunk2
    calc _ ≤ (2 : ENNReal) * ENNReal.ofReal K_BSG * ENNReal.ofReal R_ret * Nreal δ B1_norm := h
         _ = (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm := by
           simp [hKR1, mul_assoc, mul_left_comm]

  -- Bound 3: B1+B2 sum (B1 perspective)
  have h_norm3 : Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm := by
    have h := normalized_sum_transfer
      hδ_pos hB1B2_sum_bdd h_sum_B1B2_B1 h_retention_B1 h_chunk1 h_chunk2
    calc _ ≤ (2 : ENNReal) * ENNReal.ofReal K_BSG * ENNReal.ofReal R_ret * Nreal δ B1_norm := h
         _ = (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm := by
           simp [hKR1, mul_assoc, mul_left_comm]

  -- Bound 4: B2 self-diff (B2 perspective)
  have h_norm4 : Nreal δ (Set.image2 (· - ·) B2_norm B2_norm) ≤
      ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
    have h := normalized_self_difference_transfer h_diff_B2B2 h_retention_B2 h_chunk2
    calc _ ≤ ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret * Nreal δ B2_norm := h
         _ = ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
           exact congr_arg (fun x => x * Nreal δ B2_norm) hKR2

  -- Reflection: N(B1-B2) = N(B2-B1)
  have hN_B1B2_diff_eq : Nreal δ (Set.image2 (· - ·) B1 B2) = Nreal δ (Set.image2 (· - ·) B2 B1) := by
    have h_neg_eq : Set.image (fun x : ℝ => -x) (Set.image2 (· - ·) B2 B1) = Set.image2 (· - ·) B1 B2 := by
      ext z
      simp only [Set.mem_image, Set.mem_image2]
      constructor
      · rintro ⟨w, ⟨a, ha, b, hb, rfl⟩, rfl⟩
        refine ⟨b, hb, a, ha, ?_⟩; ring
      · rintro ⟨a, ha, b, hb, rfl⟩
        refine ⟨b - a, ⟨b, hb, a, ha, by ring⟩, by ring⟩
    have h_ref : Nreal δ (Set.image (fun x : ℝ => -x) (Set.image2 (· - ·) B2 B1)) =
        Nreal δ (Set.image2 (· - ·) B2 B1) :=
      nreal_reflection_eq hδ_pos hB2B1_grid hB2B1_bdd
    rw [h_neg_eq] at h_ref
    exact h_ref
  have h_diff_B1B2_B2 : Nreal δ (Set.image2 (· - ·) B1 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 := by
    rw [hN_B1B2_diff_eq]
    exact h_diff_B2B1_B2

  -- Bound 5: B1-B2 cross-diff (B2 perspective)
  have h_norm5 : Nreal δ (Set.image2 (· - ·) B1_norm B2_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
    have h := normalized_cross_difference_transfer
      hδ_pos hB1B2_diff_bdd h_diff_B1B2_B2 h_retention_B2 h_chunk2 h_chunk1
    have h_goal : (2 : ENNReal) * ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret * Nreal δ B2_norm =
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
      have h_assoc : (2 : ENNReal) * ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret =
          (2 : ENNReal) * (ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret) := by
        simp [mul_assoc]
      rw [h_assoc, hKR2] <;> simp [mul_assoc]
    rw [h_goal] at h
    exact h

  -- Bound 6: B1+B2 sum (B2 perspective)
  have h_norm6 : Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
      (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
    have h_sum_comm : Set.image2 (· + ·) B2 B1 = Set.image2 (· + ·) B1 B2 := by
      ext z
      simp only [Set.mem_image2]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        refine ⟨y, hy, x, hx, by ring⟩
      · rintro ⟨x, hx, y, hy, rfl⟩
        refine ⟨y, hy, x, hx, by ring⟩
    have h_sum_B2B1_B2 : Nreal δ (Set.image2 (· + ·) B2 B1) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 := by
      rw [h_sum_comm]; exact h_sum_B1B2_B2
    have hB2B1_sum_bdd : IsBounded (Set.image2 (· + ·) B2 B1) := by
      rw [h_sum_comm]; exact hB1B2_sum_bdd
    have h := normalized_sum_transfer
      hδ_pos hB2B1_sum_bdd h_sum_B2B1_B2 h_retention_B2 h_chunk2 h_chunk1
    have h_sum_comm_norm : Set.image2 (· + ·) B2_norm B1_norm = Set.image2 (· + ·) B1_norm B2_norm := by
      ext z
      simp only [Set.mem_image2]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        refine ⟨y, hy, x, hx, by ring⟩
      · rintro ⟨x, hx, y, hy, rfl⟩
        refine ⟨y, hy, x, hx, by ring⟩
    have h_goal : (2 : ENNReal) * ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret * Nreal δ B2_norm =
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm := by
      have h_assoc : (2 : ENNReal) * ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret =
          (2 : ENNReal) * (ENNReal.ofReal K_BSG_B2 * ENNReal.ofReal R_ret) := by
        simp [mul_assoc]
      rw [h_assoc, hKR2] <;> simp [mul_assoc]
    rw [h_goal] at h
    rw [←h_sum_comm_norm]
    exact h

  refine' ⟨B1, B2, G', C_BSG, K_BSG, K_BSG_B2, K_BSG_all, K_sector_B1, K_sector_B2,
    k, j, B1_norm, B2_norm, G_norm, G_orig, R_ret, M_ret,
    hB1_sub_S1, hB2_sub_S2, hG'_sub_Gamma, hG'_fibers, hG'_grid, hG'_nonempty,
    hB1_fin, hB2_fin, hB1_nonempty_bsg, hB2_nonempty_bsg,
    hB1_int_grid, hB2_int_grid,
    hB1_delta, hB2_delta,
    hB1_size_lower, hB2_size_lower,
    hG'_density,
    h_sec1_B1, h_sec2_B1, h_sec3_B1,
    h_sec1_B2, h_sec2_B2, h_sec3_B2,
    hK_BSG_pos, h_diff_self, h_diff_cross, h_sum_B1B2_B1,
    hK_BSG_B2_pos, h_diff_B2B2, h_diff_B2B1_B2, h_sum_B1B2_B2,
    hK_BSG_all_pos, hK_BSG_le_all, hK_BSG_B2_le_all,
    hK_BSG_all_B1, hK_BSG_all_B2, hK_BSG_all_le,
    hB1_norm_unit, hB2_norm_unit,
    hB1_norm_nonempty, hB2_norm_nonempty,
    hB1_norm_fin, hB2_norm_fin,
    hB1_norm_sep, hB2_norm_sep,
    hG_norm_fin, hG_norm_grid, hG_norm_sub,
    hG_orig_sub, hG'_witness,
    hG_norm_density_ncard,
    hR_ret_pos, hR_ret_eq, hM_ret_pos,
    (by rfl), (by dsimp only [M_ret, R1] <;> ring),
    hB1_size_lower_norm, hB2_size_lower_norm,
    hB1_norm_size_upper, hB2_norm_size_upper,
    hB1_norm_delta, hB2_norm_delta,
    h_norm1, h_norm2, h_norm3,
    h_norm4, h_norm5, h_norm6⟩

end ProductLikeIncidence.IncidenceToRingContradiction
