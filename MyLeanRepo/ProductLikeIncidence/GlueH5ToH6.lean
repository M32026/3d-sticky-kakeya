module

/-
# Glue: Helper 5 → Helper 6 Full Composition

Admission-free theorem that takes Helper 5's exact output bundle plus upstream
data (from Helpers 1–4 and outer hypotheses), applies all four H5→H6 bridges,
and invokes Helper 6 to conclude False.

Every sub-step calls an existing proved lemma. Any remaining gap is an
explicit hypothesis on this theorem, not a sorry.

## Bridges applied
1. **Factor unification** (`bridge_unify_bsg_factors`, Fjord): 6 bounds with separate
   K_BSG/K_BSG_B2/R_ret → 6 bounds with unified K_BSG
2. **Regularity absorption** (`bridge_delta_set_absorption_both`, Aurora): delta-set
   constants + absorption + size upper bounds
3. **Size lower bounds** (`bridge_size_lower_bounds_both`, Aurora): ncard retention
   → Nreal lower bounds δ^(-s+q_size)
4. **Multiplicity transport** (`bridge_multiplicity_transport`, Aurora): original
   Gamma multiplicity → normalized G_norm multiplicity
5. **Graph covering** (`bridge_graph_covering_phase7`, Aurora): ncard graph density
   → dyadicCoveringNumber with Phase7 constant

## Whiteprint node
Part of `itr_sector_translation_and_contradiction` composition.
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.ProductLikeIncidence.ProductLikeProof
public import MyLeanRepo.ProductLikeIncidence.Phase0.Phase0CompositionV3
public import MyLeanRepo.ProductLikeIncidence.Phase0.ProjectionBoundComplete
public import MyLeanRepo.ProductLikeIncidence.Phase0Absorption
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV3
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.V4NumericFills
public import MyLeanRepo.ProductLikeIncidence.ExtractionNumericConditions
public import MyLeanRepo.ProductLikeIncidence.DensityApplicationV4
public import MyLeanRepo.ProductLikeIncidence.KaufmanAbsorptionV3
public import MyLeanRepo.ProductLikeIncidence.ExactEndgameGeneralizedV3
public import MyLeanRepo.ProductLikeIncidence.Obligation3ProjectiveTransform
public import MyLeanRepo.ProductLikeIncidence.EnergyScaling
public import MyLeanRepo.ProductLikeIncidence.NormalizeAndExtract
public import MyLeanRepo.ProductLikeIncidence.ProductDensityFromThreefold
public import MyLeanRepo.ProductLikeIncidence.Phase3_4Integration
public import MyLeanRepo.ProductLikeIncidence.Phase56Integration
public import MyLeanRepo.ProductLikeIncidence.GridSeparatedCard
public import MyLeanRepo.ProductLikeIncidence.Phase7Budgets
public import MyLeanRepo.ProductLikeIncidence.Phase7FullIntegrationV2
public import MyLeanRepo.ProductLikeIncidence.Phase7ScaledProjections
public import MyLeanRepo.ProductLikeIncidence.Phase7ChartBounds
public import MyLeanRepo.ProductLikeIncidence.TranslationBounds
public import MyLeanRepo.ProductLikeIncidence.SimpleNormalize
public import MyLeanRepo.ProductLikeIncidence.NormalizeWithPopularity
public import MyLeanRepo.ProductLikeIncidence.ThickeningCovering
public import MyLeanRepo.ProductLikeIncidence.BoundedOccupancy
public import MyLeanRepo.ProductLikeIncidence.CardinalityLowerBound
public import MyLeanRepo.ProductLikeIncidence.K_A_Wrapper
public import MyLeanRepo.ProductLikeIncidence.PopularityThresholds
public import MyLeanRepo.ProductLikeIncidence.NormalizedSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal MeasureTheory Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

-- ============================================================================
-- Local bridge lemmas (defined here since scratch files cannot import each other)
-- ============================================================================

/-- Factor unification: unify separate K_BSG/K_BSG_B2 bounds into one constant. -/
lemma glue_bridge_unify_bsg_factors
    {B1 B2 : Set ℝ} {K_BSG K_BSG_B2 R_ret : ℝ} {δ : ℝ}
    (hK_BSG_pos : 0 < K_BSG) (hK_BSG_B2_pos : 0 < K_BSG_B2) (hR_ret_pos : 0 < R_ret)
    (h_diff_B1B1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1)
    (h_diff_B2B1_over_B1 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1)
    (h_sum_B1B2_over_B1 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1)
    (h_diff_B2B2 : Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2)
    (h_diff_B2B1_over_B2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2)
    (h_diff_B1B2_over_B2 : Nreal δ (Set.image2 (· - ·) B1 B2) ≤ (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2)
    (h_sum_B1B2_over_B2 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2) :
    ∃ (K_unified : ℝ), K_unified = 2 * R_ret * max K_BSG K_BSG_B2 ∧ 0 < K_unified ∧
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_unified * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_unified * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_unified * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_unified * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B1 B2) ≤ ENNReal.ofReal K_unified * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_unified * Nreal δ B2 := by
  set M : ℝ := max K_BSG K_BSG_B2 with hM_def
  set K_unified : ℝ := 2 * R_ret * M with hK_def
  have hmax1 : K_BSG ≤ M := by rw [hM_def]; exact le_max_left _ _
  have hmax2 : K_BSG_B2 ≤ M := by rw [hM_def]; exact le_max_right _ _
  have hM_pos : 0 < M := by have h : 0 < K_BSG := hK_BSG_pos; linarith [hmax1]
  have hK_pos : 0 < K_unified := by rw [hK_def]; positivity
  have hRM_nonneg : 0 ≤ R_ret * M := mul_nonneg (by linarith) (by linarith)
  have h1 : K_BSG * R_ret ≤ K_unified := by
    calc K_BSG * R_ret ≤ M * R_ret := by gcongr
      _ = R_ret * M := by ring
      _ ≤ R_ret * M + R_ret * M := by linarith
      _ = 2 * R_ret * M := by ring
      _ = K_unified := by rw [hK_def]
  have h2 : 2 * (K_BSG * R_ret) ≤ K_unified := by
    calc 2 * (K_BSG * R_ret) ≤ 2 * (M * R_ret) := by gcongr
      _ = 2 * R_ret * M := by ring
      _ = K_unified := by rw [hK_def]
  have h3 : K_BSG_B2 * R_ret ≤ K_unified := by
    calc K_BSG_B2 * R_ret ≤ M * R_ret := by gcongr
      _ = R_ret * M := by ring
      _ ≤ R_ret * M + R_ret * M := by linarith
      _ = 2 * R_ret * M := by ring
      _ = K_unified := by rw [hK_def]
  have h4 : 2 * (K_BSG_B2 * R_ret) ≤ K_unified := by
    calc 2 * (K_BSG_B2 * R_ret) ≤ 2 * (M * R_ret) := by gcongr
      _ = 2 * R_ret * M := by ring
      _ = K_unified := by rw [hK_def]
  have h_ofReal2 : ∀ (x : ℝ), (2 : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
    intro x; simp [ENNReal.ofReal_mul]
  refine' ⟨K_unified, by rw [hK_def, hM_def] <;> rfl, hK_pos, _⟩
  have h5 : ENNReal.ofReal (K_BSG * R_ret) ≤ ENNReal.ofReal K_unified := ENNReal.ofReal_le_ofReal h1
  have h6 : (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) ≤ ENNReal.ofReal K_unified := by
    rw [h_ofReal2 (K_BSG * R_ret)]; exact ENNReal.ofReal_le_ofReal h2
  have h7 : ENNReal.ofReal (K_BSG_B2 * R_ret) ≤ ENNReal.ofReal K_unified := ENNReal.ofReal_le_ofReal h3
  have h8 : (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) ≤ ENNReal.ofReal K_unified := by
    rw [h_ofReal2 (K_BSG_B2 * R_ret)]; exact ENNReal.ofReal_le_ofReal h4
  exact ⟨le_trans h_diff_B1B1 (by gcongr), le_trans h_diff_B2B1_over_B1 (by gcongr),
    le_trans h_sum_B1B2_over_B1 (by gcongr), le_trans h_diff_B2B2 (by gcongr),
    le_trans h_diff_B1B2_over_B2 (by gcongr), le_trans h_sum_B1B2_over_B2 (by gcongr)⟩

/-- Regularity absorption for both B1 and B2. -/
lemma glue_bridge_delta_set_absorption_both
    {δ κ0 εnc s : ℝ} {B1 B2 : Set ℝ} {C_BSG R_ret K_work : ℝ}
    (hC_BSG_pos : 0 < C_BSG) (hR_ret_pos : 0 < R_ret)
    (hB1_delta : IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B1)
    (hB2_delta : IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B2)
    (h_absorb : 2 * (C_BSG * R_ret) ≤ K_work * δ ^ (-εnc))
    (hB1_upper : Nreal δ B1 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hB2_upper : Nreal δ B2 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc)))) :
    ∃ (C_B1 C_B2 : ℝ),
      IsProductLikeRealDeltaSCSet δ κ0 C_B1 B1 ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_B2 B2 ∧
      2 * C_B1 ≤ K_work * δ ^ (-εnc) ∧
      2 * C_B2 ≤ K_work * δ ^ (-εnc) ∧
      Nreal δ B1 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) ∧
      Nreal δ B2 ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) := by
  refine' ⟨C_BSG * R_ret, C_BSG * R_ret, hB1_delta, hB2_delta, h_absorb, h_absorb, hB1_upper, hB2_upper⟩

/-- Size lower bounds for both B1 and B2. -/
lemma glue_bridge_size_lower_bounds_both
    {δ s : ℝ} (q_input q_size : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    {S1 S2 : Set ℝ} (hS1_finite : S1.Finite) (hS2_finite : S2.Finite)
    (hS1_lower_encard : ENat.toENNReal S1.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    (hS2_lower_encard : ENat.toENNReal S2.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    {B1 B2 : Set ℝ} (c_ret M_ret : ℝ) (hc_ret_nonneg : 0 ≤ c_ret) (hM_ret_pos : 0 < M_ret)
    (h_retention1 : c_ret * (S1.ncard : ℝ) / M_ret ≤ (B1.ncard : ℝ))
    (h_retention2 : c_ret * (S2.ncard : ℝ) / M_ret ≤ (B2.ncard : ℝ))
    (hB1_finite : B1.Finite) (hB2_finite : B2.Finite)
    (hB1_grid : ∀ x ∈ B1, x ∈ productLikeIntegerGrid δ)
    (hB2_grid : ∀ x ∈ B2, x ∈ productLikeIntegerGrid δ)
    (hB1_separated : ∀ x ∈ B1, ∀ y ∈ B1, x ≠ y → |x - y| ≥ δ)
    (hB2_separated : ∀ x ∈ B2, ∀ y ∈ B2, x ≠ y → |x - y| ≥ δ)
    (h_absorb : c_ret / M_ret * δ ^ (-s + q_input) ≥ δ ^ (-s + q_size)) :
    Nreal δ B1 ≥ ENNReal.ofReal (δ ^ (-s + q_size)) ∧
    Nreal δ B2 ≥ ENNReal.ofReal (δ ^ (-s + q_size)) := by
  have h_ncard_to_nreal : ∀ (S : Set ℝ) (hS_finite : S.Finite)
      (hS_lower : ENat.toENNReal S.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
      (B : Set ℝ) (hB_finite : B.Finite)
      (hB_grid : ∀ x ∈ B, x ∈ productLikeIntegerGrid δ)
      (hB_sep : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → |x - y| ≥ δ)
      (h_ret : c_ret * (S.ncard : ℝ) / M_ret ≤ (B.ncard : ℝ)),
      Nreal δ B ≥ ENNReal.ofReal (δ ^ (-s + q_size)) := by
    intro S hS_finite hS_lower B hB_finite hB_grid hB_sep h_ret
    have hS_ncard_lower : (δ ^ (-s + q_input)) ≤ (S.ncard : ℝ) := by
      have h3 : S.encard = ↑(hS_finite.toFinset.card) := hS_finite.encard_eq_coe_toFinset_card
      have h3' : (hS_finite.toFinset.card) = S.ncard := (Set.ncard_eq_toFinset_card S hS_finite).symm
      rw [h3'] at h3
      have h4 : ENat.toENNReal S.encard = ENNReal.ofReal (S.ncard : ℝ) := by
        rw [h3]; norm_cast
      rw [h4] at hS_lower; exact_mod_cast hS_lower
    have hB_ncard_lower : c_ret / M_ret * δ ^ (-s + q_input) ≤ (B.ncard : ℝ) := by
      have h2 : c_ret / M_ret * (S.ncard : ℝ) ≤ (B.ncard : ℝ) := by
        have h_eq : c_ret * (S.ncard : ℝ) / M_ret = c_ret / M_ret * (S.ncard : ℝ) := by ring
        rw [h_eq] at h_ret; exact h_ret
      have h3 : c_ret / M_ret * δ ^ (-s + q_input) ≤ c_ret / M_ret * (S.ncard : ℝ) := by
        apply mul_le_mul_of_nonneg_left hS_ncard_lower
        positivity
      exact le_trans h3 h2
    have h4 : δ ^ (-s + q_size) ≤ (B.ncard : ℝ) := by
      calc δ ^ (-s + q_size) ≤ c_ret / M_ret * δ ^ (-s + q_input) := h_absorb
        _ ≤ (B.ncard : ℝ) := hB_ncard_lower
    have hB_eq : Nreal δ B = ENNReal.ofReal (B.ncard : ℝ) :=
      grid_separated_nreal_eq_card1d hδ_pos hB_finite hB_grid hB_sep
    rw [hB_eq]; exact_mod_cast h4
  constructor
  · exact h_ncard_to_nreal S1 hS1_finite hS1_lower_encard B1 hB1_finite hB1_grid hB1_separated h_retention1
  · exact h_ncard_to_nreal S2 hS2_finite hS2_lower_encard B2 hB2_finite hB2_grid hB2_separated h_retention2

/-- Multiplicity transport: original Gamma multiplicity → normalized G_norm. -/
lemma glue_bridge_multiplicity_transport
    {δ : ℝ} {Y : Set ℝ} (hY_fin : Y.Finite) {x : ℝ → ℝ}
    {Gamma : Set (EuclideanSpace ℝ (Fin 2))} (c_mult : ℝ) (hc_mult_pos : 0 < c_mult)
    (S_pre_orig : ℝ → Set ℝ)
    (h_mult_orig : ∀ g ∈ Gamma,
      ({y ∈ hY_fin.toFinset | g 0 * x y + g 1 ∈ S_pre_orig y}.card : ℝ) ≥ c_mult * hY_fin.toFinset.card)
    {G_orig G_norm : Set (EuclideanSpace ℝ (Fin 2))} (k j : ℤ)
    (hG_orig_sub_Gamma : G_orig ⊆ Gamma)
    (h_norm_shift : ∀ p' ∈ G_norm, ∃ g ∈ G_orig, p' 0 = g 0 - (k : ℝ) ∧ p' 1 = g 1 - (j : ℝ))
    (S_pre : ℝ → Set ℝ)
    (hS_pre_shift : ∀ y, S_pre y = {z | z + (k : ℝ) * x y + (j : ℝ) ∈ S_pre_orig y}) :
    ∀ p' ∈ G_norm,
      ({y ∈ hY_fin.toFinset | p' 0 * x y + p' 1 ∈ S_pre y}.card : ℝ) ≥ c_mult * hY_fin.toFinset.card := by
  intro p' hp'
  rcases h_norm_shift p' hp' with ⟨g, hg_in_Gorig, h_eq0, h_eq1⟩
  have hg_in_Gamma : g ∈ Gamma := hG_orig_sub_Gamma hg_in_Gorig
  have h_mult_g : ({y ∈ hY_fin.toFinset | g 0 * x y + g 1 ∈ S_pre_orig y}.card : ℝ) ≥ c_mult * hY_fin.toFinset.card :=
    h_mult_orig g hg_in_Gamma
  have h_set_eq : {y ∈ hY_fin.toFinset | p' 0 * x y + p' 1 ∈ S_pre y} =
      {y ∈ hY_fin.toFinset | g 0 * x y + g 1 ∈ S_pre_orig y} := by
    ext y; simp only [Finset.mem_filter, Finset.mem_univ]
    constructor
    · rintro ⟨hy, h_in⟩
      have hS : S_pre y = {z | z + (k : ℝ) * x y + (j : ℝ) ∈ S_pre_orig y} := hS_pre_shift y
      have h1 : (p' 0 * x y + p' 1) + (k : ℝ) * x y + (j : ℝ) ∈ S_pre_orig y := by
        rw [hS] at h_in; exact Set.mem_setOf.mp h_in
      have h_alg : (p' 0 * x y + p' 1) + (k : ℝ) * x y + (j : ℝ) = g 0 * x y + g 1 := by
        rw [h_eq0, h_eq1] <;> ring
      rw [h_alg] at h1; exact ⟨hy, h1⟩
    · rintro ⟨hy, h_in⟩
      have h_alg : p' 0 * x y + p' 1 = (g 0 * x y + g 1) - (k : ℝ) * x y - (j : ℝ) := by
        rw [h_eq0, h_eq1] <;> ring
      have h_shift : (p' 0 * x y + p' 1) + (k : ℝ) * x y + (j : ℝ) ∈ S_pre_orig y := by
        have h_eq : (p' 0 * x y + p' 1) + (k : ℝ) * x y + (j : ℝ) = g 0 * x y + g 1 := by
          rw [h_alg] <;> ring
        rw [h_eq]; exact h_in
      have h_in_Spre : p' 0 * x y + p' 1 ∈ S_pre y := by
        rw [hS_pre_shift y]; simpa using h_shift
      exact ⟨hy, h_in_Spre⟩
  rw [h_set_eq]; exact h_mult_g

/-- Graph covering: ncard density → dyadicCoveringNumber with Phase7 constant. -/
lemma glue_bridge_graph_covering_phase7
    {δ : ℝ} (hδ_pos : 0 < δ)
    {G : Set (EuclideanSpace ℝ (Fin 2))} (hG_finite : G.Finite)
    (hG_grid : ∀ z ∈ G, ∀ i : Fin 2, z i ∈ productLikeIntegerGrid δ)
    (hG_separated : ∀ z ∈ G, ∀ w ∈ G, z ≠ w → dist z w ≥ δ)
    {B1 : Set ℝ} (hB1_finite : B1.Finite)
    (hB1_grid : ∀ x ∈ B1, x ∈ productLikeIntegerGrid δ)
    (hB1_separated : ∀ x ∈ B1, ∀ y ∈ B1, x ≠ y → |x - y| ≥ δ)
    {B2 : Set ℝ} (hB2_finite : B2.Finite)
    (hB2_grid : ∀ x ∈ B2, x ∈ productLikeIntegerGrid δ)
    (hB2_separated : ∀ x ∈ B2, ∀ y ∈ B2, x ≠ y → |x - y| ≥ δ)
    (c_ret : ℝ) (hc_ret_nonneg : 0 ≤ c_ret)
    (h_density_ncard : c_ret * (B1.ncard : ℝ) * (B2.ncard : ℝ) ≤ (G.ncard : ℝ))
    (c_mult_dir c_proj : ℝ) (hc_mult_dir_pos : 0 < c_mult_dir) (hc_proj_nonneg : 0 ≤ c_proj)
    (h_absorb : c_ret ≥ (2 / c_mult_dir) * c_proj) :
    ENat.toENNReal (dyadicCoveringNumber δ G) ≥
      ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 := by
  have hG_eq : ENat.toENNReal (dyadicCoveringNumber δ G) = ENNReal.ofReal (G.ncard : ℝ) :=
    grid_separated_nreal_eq_card hδ_pos hG_finite hG_grid hG_separated
  have hB1_eq : Nreal δ B1 = ENNReal.ofReal (B1.ncard : ℝ) :=
    grid_separated_nreal_eq_card1d hδ_pos hB1_finite hB1_grid hB1_separated
  have hB2_eq : Nreal δ B2 = ENNReal.ofReal (B2.ncard : ℝ) :=
    grid_separated_nreal_eq_card1d hδ_pos hB2_finite hB2_grid hB2_separated
  have h_covering : ENNReal.ofReal c_ret * Nreal δ B1 * Nreal δ B2 ≤ ENat.toENNReal (dyadicCoveringNumber δ G) := by
    rw [hG_eq, hB1_eq, hB2_eq]
    have h_main : ENNReal.ofReal c_ret * ENNReal.ofReal (B1.ncard : ℝ) * ENNReal.ofReal (B2.ncard : ℝ) ≤ ENNReal.ofReal (G.ncard : ℝ) := by
      rw [← ENNReal.ofReal_mul hc_ret_nonneg, ← ENNReal.ofReal_mul (by positivity)]
      <;> exact_mod_cast h_density_ncard
    exact h_main
  have h_const_le : ENNReal.ofReal ((2 / c_mult_dir) * c_proj) ≤ ENNReal.ofReal c_ret := by
    gcongr <;> linarith
  have h_phase7_eq : ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj = ENNReal.ofReal ((2 / c_mult_dir) * c_proj) := by
    rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
  have h_main : ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj * Nreal δ B1 * Nreal δ B2 ≤
      ENNReal.ofReal c_ret * Nreal δ B1 * Nreal δ B2 := by
    rw [h_phase7_eq]; gcongr
  exact le_trans h_main h_covering

/-- **Full H5→H6 composition**: Given Helper 5 outputs and all upstream data,
apply all bridges and invoke Helper 6 to conclude False.

This theorem is admission-free: every sub-step calls a proved lemma. Any
remaining integration gap is an explicit hypothesis. -/
theorem glue_h5_to_h6
    -- ========================================================================
    -- UPSTREAM INPUTS (everything not derived from Helper 5)
    -- ========================================================================
    {δ s τ κ0 η η_work ε ε_mass εgain εnc : ℝ}
    {L_exp p_projective : ℝ}
    -- Basic
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hτ_pos : 0 < τ)
    (hkappa_pos : 0 < κ0)
    (hκ0_lt_s : κ0 < s)
    (hκ0_le_tau : κ0 ≤ τ)
    (hε_pos : 0 < ε) (hε_mass_pos : 0 < ε_mass) (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (h10ε_lt_η_work : 10 * ε < η_work)
    (h5η_work_lt : 5 * η_work < 2 * (s - κ0))
    (h4η_work_lt_tau : 4 * η_work < τ)
    (hL_exp_pos : 0 < L_exp)
    (hL_exp_eq_seven : L_exp = 7)
    (hη_work_le_kappa0 : η_work ≤ κ0)
    (hp_ge_10 : 10 ≤ p_projective)
    -- Budget
    (q_graph_total q_diff q_size ζ_dir η_proj : ℝ)
    (h_q_graph_total_nonneg : 0 ≤ q_graph_total)
    (h_q_diff_nonneg : 0 ≤ q_diff)
    (h_q_size_nonneg : 0 ≤ q_size)
    (hζ_dir_nonneg : 0 ≤ ζ_dir)
    (hη_proj_nonneg : 0 ≤ η_proj)
    (h_budget : εgain > q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)
    (h_proj_budget : (L_exp - 1 / 2 : ℝ) * η < ζ_dir + η_proj)
    -- Numeric
    (hG_eta_work_le : gapCoefficientV4 L_exp κ0 p_projective τ * η_work ≤ εnc / 2)
    (h_small_bsg : η_work ≤ εnc / (2 * bsgOverheadCoefficientV4 L_exp κ0 p_projective))
    (hrho_sel_pos : 0 < rhoSelDefault η_work)
    (hrho_sep_pos : 0 < rhoSepDefault η_work κ0)
    -- Graph constants
    (C_raw C_Pbar c_proj K_work : ℝ)
    (hC_raw_pos : 0 < C_raw)
    (hC_Pbar_pos : 0 < C_Pbar)
    (hc_proj_pos : 0 < c_proj)
    (hεgain_pos : 0 < εgain)
    (hc_proj_ge : c_proj ≥ δ ^ q_graph_total)
    (h_delta_small : δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64)
    (h_factor_absorb : 6 * C_raw * Real.sqrt C_Pbar * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) < 1)
    -- Direction transport
    (q_pole C_ν L_chart : ℝ)
    (hq_pole_pos : 0 < q_pole)
    (hC_ν_pos : 0 < C_ν)
    (hL_chart_pos : 0 < L_chart)
    (hL_chart_ge_one : 1 ≤ L_chart)
    (hL_chart_ge : L_chart ≥ δ ^ (-2 * q_pole))
    -- Phase0
    {Y : Set ℝ}
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν_frost : IsDirectionFrostman δ τ C_ν ν)
    (hY_sub_unit : Y ⊆ Set.Icc 0 1)
    (hY_fin : Y.Finite)
    (hY_mass : ν Y ≥ ENNReal.ofReal (δ ^ ε_mass))
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_bdd : IsBounded Pbar_param)
    (T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
    (hT_sub : ∀ y ∈ Y, T_y_points y ⊆ Pbar_param)
    -- Phase3
    (θ1 θ2 θ3 : ℝ)
    (hθ1_in_Icc : θ1 ∈ Set.Icc 0 1)
    (hθ2_in_Icc : θ2 ∈ Set.Icc 0 1)
    (hθ3_in_Icc : θ3 ∈ Set.Icc 0 1)
    (h_ord13 : θ1 < θ3)
    (h_ord32 : θ3 < θ2)
    (h_sep13 : |θ1 - θ3| ≥ δ ^ q_pole)
    (h_sep23 : |θ2 - θ3| ≥ δ ^ q_pole)
    -- Phase4
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (S_pre : ℝ → Set ℝ)
    (hS_pre_thick : ∀ y ∈ Y, y ≠ θ2 → S_pre y ⊆
      intervalThicken (δ * (1 + |x y|) / 2) (phase7ScaledProjection y θ2 θ3 (T_y_points y)))
    (h_raw_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) (T_y_points y)) ≤
      ENNReal.ofReal C_raw * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)))
    -- Double counting constant (needed for mass budget)
    (c_mult_dir : ℝ)
    (hc_mult_dir_pos : 0 < c_mult_dir)
    (hc_mult_dir_le_one : c_mult_dir ≤ 1)
    -- Uniform measure, mass budget
    (hν_uniform : ∀ y ∈ Y, ν {y} = ENNReal.ofReal (1 / (Y.ncard : ℝ)))
    (h_mass_budget : δ ^ ε_mass ≤ c_mult_dir / 2)
    -- Ring spec
    (h_ring_spec :
      ∀ (A : Set ℝ) (μ : Measure ℝ),
        A ⊆ Set.Icc 1 2 →
        IsProductLikeRealDeltaSCSet δ κ0 (K_work * δ ^ (-εnc)) A →
        Nreal δ A ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))) →
        IsDirectionFrostman δ κ0 (K_work * δ ^ (-εnc)) μ →
        ∃ x_dir ∈ μ.support,
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ A ≤
            Nreal δ (Set.image2 (fun a b => a + x_dir * b) A A))
    (hK_work_ge1 : 1 ≤ K_work)
    (hPbar_small : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) <
        ENNReal.ofReal (C_Pbar * δ ^ (-(2 * s + η))))
    (h_sector_absorb : C_ν * δ ^ τ ≤ δ ^ ε_mass / 2)
    (h_frostman_budget : C_ν * (8 : ℝ) * δ ^ (-ε_mass) * L_chart ^ τ ≤ K_work * δ ^ (-εnc))
    (h_chartFullLambda_bound : ∀ (i : Fin 4) (y : ℝ), sectorPredicate i x y →
      |chartFullLambda i y θ1 θ3 θ2 x| ≤ 1)
    -- ========================================================================
    -- HELPER 5 OUTPUTS
    -- ========================================================================
    {B1_norm B2_norm : Set ℝ}
    {G' G_norm G_orig : Set (EuclideanSpace ℝ (Fin 2))}
    {C_BSG K_BSG K_BSG_B2 R_ret M_ret : ℝ}
    (k j : ℤ)
    -- Normalized set basics
    (hB1_grid : B1_norm ⊆ productLikeUnitGrid δ)
    (hB2_grid : B2_norm ⊆ productLikeUnitGrid δ)
    (hB1_nonempty : B1_norm.Nonempty)
    (hB2_nonempty : B2_norm.Nonempty)
    (hB1_finite : B1_norm.Finite)
    (hB2_finite : B2_norm.Finite)
    (hB1_sep : ∀ x ∈ B1_norm, ∀ y ∈ B1_norm, x ≠ y → |x - y| ≥ δ)
    (hB2_sep : ∀ x ∈ B2_norm, ∀ y ∈ B2_norm, x ≠ y → |x - y| ≥ δ)
    -- Normalized graph
    (hG_norm_finite : G_norm.Finite)
    (hG_norm_grid : ∀ p ∈ G_norm, ∀ i : Fin 2, ∃ m : ℤ, p i = δ * (m : ℝ))
    (hG_norm_sub : G_norm ⊆ {p | p 0 ∈ B1_norm ∧ p 1 ∈ B2_norm})
    (hG_orig_sub : G_orig ⊆ G')
    (h_norm_shift : ∀ p' ∈ G_norm, ∃ g ∈ G_orig,
      p' 0 = g 0 - (k : ℝ) ∧ p' 1 = g 1 - (j : ℝ))
    (hG_norm_separated : ∀ z ∈ G_norm, ∀ w ∈ G_norm, z ≠ w → dist z w ≥ δ)
    -- Graph density (ncard format)
    (c_ret : ℝ)
    (hc_ret_nonneg : 0 ≤ c_ret)
    (h_density_ncard : c_ret * (B1_norm.ncard : ℝ) * (B2_norm.ncard : ℝ) ≤ (G_norm.ncard : ℝ))
    (hM_ret_pos : 0 < M_ret)
    -- Delta-set
    (hC_BSG_pos : 0 < C_BSG)
    (hR_ret_pos : 0 < R_ret)
    (hB1_delta : IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B1_norm)
    (hB2_delta : IsProductLikeRealDeltaSCSet δ κ0 (C_BSG * R_ret) B2_norm)
    -- 6 normalized bounds (B1-relative)
    (h_diff_B1B1_raw : Nreal δ (Set.image2 (· - ·) B1_norm B1_norm) ≤
        ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm)
    (h_diff_B2B1_over_B1_raw : Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm)
    (h_sum_B1B2_over_B1_raw : Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG * R_ret) * Nreal δ B1_norm)
    -- 6 normalized bounds (B2-relative)
    (h_diff_B2B2_raw : Nreal δ (Set.image2 (· - ·) B2_norm B2_norm) ≤
        ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm)
    (h_diff_B2B1_over_B2_raw : Nreal δ (Set.image2 (· - ·) B2_norm B1_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm)
    (h_sum_B1B2_over_B2_raw : Nreal δ (Set.image2 (· + ·) B1_norm B2_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm)
    -- ========================================================================
    -- BRIDGE HYPOTHESES (explicit gaps from upstream)
    -- ========================================================================
    -- Size bridge: S1/S2 lower bounds and absorption
    (q_input : ℝ)
    {S1 S2 : Set ℝ}
    (hS1_finite : S1.Finite)
    (hS2_finite : S2.Finite)
    (hS1_lower_encard : ENat.toENNReal S1.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    (hS2_lower_encard : ENat.toENNReal S2.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    -- Retention bounds (from Helper5)
    (h_retention1 : c_ret * (S1.ncard : ℝ) / M_ret ≤ (B1_norm.ncard : ℝ))
    (h_retention2 : c_ret * (S2.ncard : ℝ) / M_ret ≤ (B2_norm.ncard : ℝ))
    (h_size_absorb : c_ret / M_ret * δ ^ (-s + q_input) ≥ δ ^ (-s + q_size))
    -- Regularity bridge: size upper bounds (from upstream Pbar/projection chain)
    (hB1_upper : Nreal δ B1_norm ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (hB2_upper : Nreal δ B2_norm ≤ ENNReal.ofReal (K_work * δ ^ (-(s + εnc))))
    (h_reg_absorb : 2 * (C_BSG * R_ret) ≤ K_work * δ ^ (-εnc))
    -- Multiplicity bridge: original Gamma data
    {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    (S_pre_orig : ℝ → Set ℝ)
    (h_mult_orig : ∀ g ∈ Gamma,
      ({y ∈ hY_fin.toFinset | g 0 * x y + g 1 ∈ S_pre_orig y}.card : ℝ)
        ≥ c_mult_dir * hY_fin.toFinset.card)
    (hG_orig_sub_Gamma : G_orig ⊆ Gamma)
    (hS_pre_shift : ∀ y, S_pre y = {z | z + (k : ℝ) * x y + (j : ℝ) ∈ S_pre_orig y})
    -- Graph bridge: Phase7 constant absorption
    (hc_proj_nonneg : 0 ≤ c_proj)
    (h_graph_absorb : c_ret ≥ (2 / c_mult_dir) * c_proj)
    -- Factor unification: K_BSG, K_BSG_B2 positivity
    (hK_BSG_pos : 0 < K_BSG)
    (hK_BSG_B2_pos : 0 < K_BSG_B2)
    -- Unified K_BSG for Helper6
    (K_BSG_unified : ℝ)
    (hK_BSG_unified_pos : 0 < K_BSG_unified)
    (hK_BSG_unified_le : K_BSG_unified ≤ δ ^ (-q_diff))
    (h_unified_def : K_BSG_unified = 2 * R_ret * max K_BSG K_BSG_B2)
    -- Missing B1-B2 difference bound (symmetry gap)
    (h_diff_B1B2_over_B2_raw : Nreal δ (Set.image2 (· - ·) B1_norm B2_norm) ≤
        (2 : ENNReal) * ENNReal.ofReal (K_BSG_B2 * R_ret) * Nreal δ B2_norm) :
    False := by
  -- ========================================================================
  -- Step 1: Factor unification (Bridge A)
  -- ========================================================================
  rcases glue_bridge_unify_bsg_factors
    (hK_BSG_pos := hK_BSG_pos)
    (hK_BSG_B2_pos := hK_BSG_B2_pos)
    (hR_ret_pos := hR_ret_pos)
    (h_diff_B1B1 := h_diff_B1B1_raw)
    (h_diff_B2B1_over_B1 := h_diff_B2B1_over_B1_raw)
    (h_sum_B1B2_over_B1 := h_sum_B1B2_over_B1_raw)
    (h_diff_B2B2 := h_diff_B2B2_raw)
    (h_diff_B2B1_over_B2 := h_diff_B2B1_over_B2_raw)
    (h_diff_B1B2_over_B2 := h_diff_B1B2_over_B2_raw)
    (h_sum_B1B2_over_B2 := h_sum_B1B2_over_B2_raw)
    with ⟨K_unified, hK_unified_def, hK_unified_pos, h_diff_B1B1, h_diff_B2B1, h_sum_B1B2_over_B1,
      h_diff_B2B2, h_diff_B1B2, h_sum_B1B2_over_B2⟩

  have hK_unified_eq : K_unified = K_BSG_unified := by
    rw [hK_unified_def, h_unified_def]

  -- ========================================================================
  -- Step 2: Regularity absorption (Bridge B)
  -- ========================================================================
  rcases glue_bridge_delta_set_absorption_both
    (hC_BSG_pos := hC_BSG_pos)
    (hR_ret_pos := hR_ret_pos)
    (hB1_delta := hB1_delta)
    (hB2_delta := hB2_delta)
    (h_absorb := h_reg_absorb)
    (hB1_upper := hB1_upper)
    (hB2_upper := hB2_upper)
    with ⟨C_B1, C_B2, hB1_delta_kappa, hB2_delta_kappa, hC1_absorb, hC2_absorb,
      hB1_upper', hB2_upper'⟩

  -- ========================================================================
  -- Step 3: Size lower bounds (Bridge C)
  -- ========================================================================
  rcases @glue_bridge_size_lower_bounds_both δ s q_input q_size hδ_pos hδ_lt_one
    S1 S2 hS1_finite hS2_finite hS1_lower_encard hS2_lower_encard
    B1_norm B2_norm c_ret M_ret hc_ret_nonneg hM_ret_pos h_retention1 h_retention2
    hB1_finite hB2_finite
    (fun x hx => (hB1_grid hx).1)
    (fun x hx => (hB2_grid hx).1)
    hB1_sep hB2_sep h_size_absorb
    with ⟨hB1_lower, hB2_lower⟩

  -- ========================================================================
  -- Step 4: Multiplicity transport (Bridge D)
  -- ========================================================================
  have h_point_mult : ∀ p' ∈ G_norm,
      ({y ∈ hY_fin.toFinset | p' 0 * x y + p' 1 ∈ S_pre y}.card : ℝ)
        ≥ c_mult_dir * hY_fin.toFinset.card :=
    glue_bridge_multiplicity_transport
      (δ := δ)
      (hY_fin := hY_fin)
      (x := x)
      (Gamma := Gamma)
      (c_mult := c_mult_dir)
      (hc_mult_pos := hc_mult_dir_pos)
      (S_pre_orig := S_pre_orig)
      (h_mult_orig := h_mult_orig)
      (k := k) (j := j)
      (hG_orig_sub_Gamma := hG_orig_sub_Gamma)
      (h_norm_shift := h_norm_shift)
      (S_pre := S_pre)
      (hS_pre_shift := hS_pre_shift)

  -- ========================================================================
  -- Step 5: Graph covering (Bridge E)
  -- ========================================================================
  have hF_graph_covering : ENat.toENNReal (dyadicCoveringNumber δ G_norm) ≥
      ENNReal.ofReal (2 / c_mult_dir) * ENNReal.ofReal c_proj *
        Nreal δ B1_norm * Nreal δ B2_norm :=
    glue_bridge_graph_covering_phase7
      (hδ_pos := hδ_pos)
      (hG_finite := hG_norm_finite)
      (hG_grid := fun p hp i => hG_norm_grid p hp i)
      (hG_separated := hG_norm_separated)
      (hB1_finite := hB1_finite)
      (hB1_grid := fun x hx => (hB1_grid hx).1)
      (hB1_separated := hB1_sep)
      (hB2_finite := hB2_finite)
      (hB2_grid := fun x hx => (hB2_grid hx).1)
      (hB2_separated := hB2_sep)
      (c_ret := c_ret)
      (hc_ret_nonneg := hc_ret_nonneg)
      (h_density_ncard := h_density_ncard)
      (c_mult_dir := c_mult_dir)
      (c_proj := c_proj)
      (hc_mult_dir_pos := hc_mult_dir_pos)
      (hc_proj_nonneg := hc_proj_nonneg)
      (h_absorb := h_graph_absorb)

  -- ========================================================================
  -- Step 6: Boundedness from finite + unit grid
  -- ========================================================================
  have hB1_bounded : IsBounded B1_norm := by
    have h : B1_norm ⊆ Set.Icc (0 : ℝ) 1 := fun x hx => (hB1_grid hx).2
    have hI : IsBounded (Set.Icc (0 : ℝ) 1) := Metric.isBounded_Icc 0 1
    exact hI.subset h
  have hB2_bounded : IsBounded B2_norm := by
    have h : B2_norm ⊆ Set.Icc (0 : ℝ) 1 := fun x hx => (hB2_grid hx).2
    have hI : IsBounded (Set.Icc (0 : ℝ) 1) := Metric.isBounded_Icc 0 1
    exact hI.subset h

  -- ========================================================================
  -- Step 7: Call Helper 6
  -- ========================================================================
  exact phase7_full_integration_v2
    (p_projective := p_projective)
    (hδ_pos := hδ_pos)
    (hδ_lt_one := hδ_lt_one)
    (hδ_dyadic := hδ_dyadic)
    (hs_pos := hs_pos)
    (hs_lt_one := hs_lt_one)
    (hτ_pos := hτ_pos)
    (hkappa_pos := hkappa_pos)
    (hκ0_lt_s := hκ0_lt_s)
    (hκ0_le_tau := hκ0_le_tau)
    (hε_pos := hε_pos)
    (hε_mass_pos := hε_mass_pos)
    (hη_pos := hη_pos)
    (q_graph_total := q_graph_total)
    (q_diff := q_diff)
    (q_size := q_size)
    (ζ_dir := ζ_dir)
    (η_proj := η_proj)
    (h_q_graph_total_nonneg := h_q_graph_total_nonneg)
    (h_q_diff_nonneg := h_q_diff_nonneg)
    (h_q_size_nonneg := h_q_size_nonneg)
    (hζ_dir_nonneg := hζ_dir_nonneg)
    (hη_proj_nonneg := hη_proj_nonneg)
    (h_budget := h_budget)
    (h_proj_budget := h_proj_budget)
    (C_raw := C_raw)
    (C_Pbar := C_Pbar)
    (c_proj := c_proj)
    (K_BSG := K_BSG_unified)
    (K_work := K_work)
    (hC_raw_pos := hC_raw_pos)
    (hC_Pbar_pos := hC_Pbar_pos)
    (hc_proj_pos := hc_proj_pos)
    (hK_BSG_pos := hK_BSG_unified_pos)
    (hεgain_pos := hεgain_pos)
    (hK_BSG_le := hK_BSG_unified_le)
    (hc_proj_ge := hc_proj_ge)
    (h_delta_small := h_delta_small)
    (h_factor_absorb := h_factor_absorb)
    (q_pole := q_pole)
    (C_ν := C_ν)
    (L_chart := L_chart)
    (hq_pole_pos := hq_pole_pos)
    (hC_ν_pos := hC_ν_pos)
    (hL_chart_pos := hL_chart_pos)
    (hL_chart_ge_one := hL_chart_ge_one)
    (hL_chart_ge := hL_chart_ge)
    (Y := Y)
    (ν := ν)
    (hν_frost := hν_frost)
    (hY_sub_unit := hY_sub_unit)
    (hY_fin := hY_fin)
    (hY_mass := hY_mass)
    (Pbar_param := Pbar_param)
    (hPbar_bdd := hPbar_bdd)
    (T_y_points := T_y_points)
    (hT_sub := hT_sub)
    (θ1 := θ1)
    (θ2 := θ2)
    (θ3 := θ3)
    (hθ1_in_Icc := hθ1_in_Icc)
    (hθ2_in_Icc := hθ2_in_Icc)
    (hθ3_in_Icc := hθ3_in_Icc)
    (h_ord13 := h_ord13)
    (h_ord32 := h_ord32)
    (h_sep13 := h_sep13)
    (h_sep23 := h_sep23)
    (x := x)
    (hx_formula := hx_formula)
    (S_pre := S_pre)
    (hS_pre_thick := hS_pre_thick)
    (h_raw_proj_bound := h_raw_proj_bound)
    (F_graph := G_norm)
    (hF_graph_finite := hG_norm_finite)
    (hF_graph_grid := hG_norm_grid)
    (B1 := B1_norm)
    (B2 := B2_norm)
    (hF_graph_sub := hG_norm_sub)
    (hB1_grid_set := hB1_grid)
    (hB2_grid_set := hB2_grid)
    (hB1_bounded := hB1_bounded)
    (hB2_bounded := hB2_bounded)
    (hB1_nonempty := hB1_nonempty)
    (hB2_nonempty := hB2_nonempty)
    (hB1_lower := hB1_lower)
    (hB2_lower := hB2_lower)
    (C_B1 := C_B1)
    (C_B2 := C_B2)
    (hB1_delta_kappa := hB1_delta_kappa)
    (hB2_delta_kappa := hB2_delta_kappa)
    (hC1_absorb := hC1_absorb)
    (hC2_absorb := hC2_absorb)
    (hB1_upper := hB1_upper')
    (hB2_upper := hB2_upper')
    (h_diff_B1B1 := by
      have h : ENNReal.ofReal K_unified = ENNReal.ofReal K_BSG_unified := by rw [hK_unified_eq]
      rw [h] at h_diff_B1B1; exact h_diff_B1B1)
    (h_diff_B2B2 := by
      have h : ENNReal.ofReal K_unified = ENNReal.ofReal K_BSG_unified := by rw [hK_unified_eq]
      rw [h] at h_diff_B2B2; exact h_diff_B2B2)
    (h_diff_B2B1 := by
      have h : ENNReal.ofReal K_unified = ENNReal.ofReal K_BSG_unified := by rw [hK_unified_eq]
      rw [h] at h_diff_B2B1; exact h_diff_B2B1)
    (h_diff_B1B2 := by
      have h : ENNReal.ofReal K_unified = ENNReal.ofReal K_BSG_unified := by rw [hK_unified_eq]
      rw [h] at h_diff_B1B2; exact h_diff_B1B2)
    (h_sum_B1B2_over_B1 := by
      have h : ENNReal.ofReal K_unified = ENNReal.ofReal K_BSG_unified := by rw [hK_unified_eq]
      rw [h] at h_sum_B1B2_over_B1; exact h_sum_B1B2_over_B1)
    (h_sum_B1B2_over_B2 := by
      have h : ENNReal.ofReal K_unified = ENNReal.ofReal K_BSG_unified := by rw [hK_unified_eq]
      rw [h] at h_sum_B1B2_over_B2; exact h_sum_B1B2_over_B2)
    (c_mult_dir := c_mult_dir)
    (hc_mult_dir_pos := hc_mult_dir_pos)
    (hc_mult_dir_le_one := hc_mult_dir_le_one)
    (h_point_mult := h_point_mult)
    (hF_graph_covering := hF_graph_covering)
    (hν_uniform := hν_uniform)
    (h_mass_budget := h_mass_budget)
    (h_ring_spec := h_ring_spec)
    (hK_work_ge1 := hK_work_ge1)
    (hPbar_small := hPbar_small)
    (h_sector_absorb := h_sector_absorb)
    (h_frostman_budget := h_frostman_budget)
    (h_chartFullLambda_bound := h_chartFullLambda_bound)

end ProductLikeIncidence.ProductReduction
