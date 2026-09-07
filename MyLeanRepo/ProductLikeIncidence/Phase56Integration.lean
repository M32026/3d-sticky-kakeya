module

/-
# Phase 5-6 Integration: BSG Extraction → Full Sector Ledger

Takes the rounded dense graph (Phase 4 output), applies BSG extraction via
`bsg_corollary`, converts the sumset bound to the FULL sector ledger using
`bsg_to_wrapper_bounds`, including all 4 difference bounds and both denominator
constants for sector-specific normalization.

## Full ledger returned

- K_sector_B1 : ENNReal — bounds normalized by N(B1)
- K_sector_B2 : ENNReal — bounds normalized by N(B2)
- All 4 bounds: B1-B1, B2-B2, B2-B1, B1+B2 (each in both normalizations)
- K_BSG : ℝ — wrapper-ready real constant with h_diff1, h_diff2

## Sector selection (done LATER, not here):
- Sector 0 (first=B2): use K_sector_B2 normalization
- Sector 1 (first=B1): use K_sector_B1 normalization
- Sector 2 (first=-B2): use K_sector_B2 (sign flip preserves covering numbers)
- Sector 3 (first=-B1): use K_sector_B1 (sign flip preserves covering numbers)

## Exponents (NOT zero loss)
- q_graph = 22*q_K (graph density loss, positive)
- q_diff, q_A remain positive and are absorbed in final Ring budget

## Main lemma

`phase56_bsg_to_wrapper_inputs`

## Whiteprint node
`phase56_integration`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.Compat
public import MyLeanRepo.IsRealDeltaSetInheritance
public import MyLeanRepo.Energy.EnergyToNonConcentration
public import MyLeanRepo.ProductLikeIncidence.BsgToWrapperBounds
public import MyLeanRepo.ThreeDirectionBSG
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open Set ENNReal Bornology MeasureTheory Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Weaken the regularity constant of a product-like δ-set.
If C1 ≤ C2, a (δ,s,C1)-set is also a (δ,s,C2)-set. -/
private lemma weaken_delta_set_constant {δ s C1 C2 : ℝ} {A : Set ℝ}
    (h : IsProductLikeRealDeltaSCSet δ s C1 A) (hC : C1 ≤ C2) :
    IsProductLikeRealDeltaSCSet δ s C2 A := by
  have hC1_pos : 0 < C1 := h.2.2.2.2.2.2.2.1
  have hC2_pos : 0 < C2 := by linarith
  have h5 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := by
    apply ENNReal.ofReal_le_ofReal; linarith
  refine' ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, hC2_pos, _⟩
  intro r Q hr hQ hδr hr1
  have h_reg := h.2.2.2.2.2.2.2.2 hr hQ hδr hr1
  have h6 : ENNReal.ofReal C1 * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) *
      ENNReal.ofReal (r ^ s) ≤
    ENNReal.ofReal C2 * ENat.toENNReal (dyadicCoveringNumber δ (productLikeRealLineCopy A)) *
      ENNReal.ofReal (r ^ s) := by gcongr
  exact le_trans h_reg h6

/-- Nreal of a bounded nonempty set is positive. -/
private lemma nreal_pos {δ : ℝ} (hδ : 0 < δ) {A : Set ℝ}
    (hA_bdd : Bornology.IsBounded A) (hA_nonempty : A.Nonempty) : 0 < Nreal δ A := by
  rcases hA_nonempty with ⟨x, hx⟩
  let g : Fin 1 → ℝ := fun (_ : Fin 1) => x
  let p : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 (Fin 1 → ℝ)).symm g
  have h_p0 : p 0 = x := by simp [p, g]
  have hp : p ∈ realLineCopy A := by
    have h : p 0 ∈ A := by rw [h_p0] <;> exact hx
    simpa [realLineCopy] using h
  have h1 : (realLineCopy A).Nonempty := ⟨p, hp⟩
  have h2 : 0 < dyadicCoveringNumber δ (realLineCopy A) :=
    robust_projection.dyadic_covering_number_pos hδ h1
  have h3 : 0 < ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by
    exact_mod_cast h2
  simpa [Nreal] using h3

/-- Nreal of the empty set is zero. -/
private lemma nreal_empty {δ : ℝ} : Nreal δ (∅ : Set ℝ) = 0 := by
  delta Nreal dyadicCoveringNumber
  have h3 : dyadicCubesMeeting δ (realLineCopy (∅ : Set ℝ)) = ∅ := by
    ext Q; simp [dyadicCubesMeeting, realLineCopy]
  rw [h3]
  <;> simp

/-- Phase 5-6 integration: from rounded graph to full sector ledger. -/
lemma phase56_bsg_to_wrapper_inputs
    {δ s κ0 q_K q_input qDiffV3 qSizeLossV3 qKA qAbsorb θ_num C_A C_sum c_dense : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hκ0_pos : 0 < κ0) (hκ0_lt_s : κ0 < s)
    (hq_K_pos : 0 < q_K) (hθ_num_pos : 0 < θ_num)
    (hC_A_pos : 0 < C_A) (hC_sum_pos : 0 < C_sum)
    (hc_dense_pos : 0 < c_dense)
    (hqKA_nonneg : 0 ≤ qKA)
    (hqAbsorb_nonneg : 0 ≤ qAbsorb)
    (hq_input_nonneg : 0 ≤ q_input)
    (hqSizeLossV3_pos : 0 < qSizeLossV3)
    -- Absorption conditions
    (h_absorb_ret : δ ^ θ_num ≤ 1 / (3 ^ 10 : ℝ))
    (h_absorb_KBSG : (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 ≤ δ ^ (-qAbsorb))
    (h_absorb_size : δ ^ (qSizeLossV3 - q_input - 10 * q_K) ≤ 1 / (3 ^ 10 : ℝ))
    -- Parameter calibration
    (hC_sum_le : C_sum ≤ δ ^ (-q_K))
    (hc_dense_ge : c_dense ≥ δ ^ q_K)
    (hqDiffV3_eq : qDiffV3 = 80 * q_K + 2 * qKA + qAbsorb)
    (hqSizeLossV3_ge : q_input + 10 * q_K ≤ qSizeLossV3)
    {K_A : ENNReal}
    {S1 S2 : Set ℝ}
    {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    (hS1_le_S2 : Nreal δ S1 ≤ K_A * Nreal δ S2)
    (hS2_le_S1 : Nreal δ S2 ≤ K_A * Nreal δ S1)
    (hK_A_ge_one : 1 ≤ K_A)
    (hK_A_ne_top : K_A ≠ ⊤)
    (hK_A_le : K_A ≤ ENNReal.ofReal (δ ^ (-qKA)))
    (hS1_lower : ENat.toENNReal S1.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    (hS2_lower : ENat.toENNReal S2.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)))
    -- S1, S2 properties
    (hS1_delta : IsProductLikeRealDeltaSCSet δ κ0 C_A S1)
    (hS2_delta : IsProductLikeRealDeltaSCSet δ κ0 C_A S2)
    (hS1_nonempty : S1.Nonempty) (hS2_nonempty : S2.Nonempty)
    (hS1_fin : S1.Finite) (hS2_fin : S2.Finite)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    -- Gamma properties
    (hGamma_sub : ∀ p ∈ Gamma, p 0 ∈ S1 ∧ p 1 ∈ S2)
    (hGamma_fin : Gamma.Finite)
    (hGamma_nonempty : Gamma.Nonempty)
    (hGamma_grid : ∀ p ∈ Gamma, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ))
    -- Density: N(Gamma) ≥ c_dense * N(S1) * N(S2)
    (hGamma_dense : ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
      ENNReal.ofReal c_dense * Nreal δ S1 * Nreal δ S2)
    -- Sumset bound
    (h_sumset : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      ENNReal.ofReal C_sum *
        ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal))) :
    ∃ (B1 B2 : Set ℝ)
      (G' : Set (EuclideanSpace ℝ (Fin 2)))
      (K_BSG K_BSG_B2 K_BSG_all : ℝ)
      (K_sector_B1 K_sector_B2 : ENNReal),
      B1 ⊆ S1 ∧ B2 ⊆ S2 ∧
      G' ⊆ Gamma ∧
      (∀ p ∈ G', p 0 ∈ B1 ∧ p 1 ∈ B2) ∧
      (∀ p ∈ G', ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
      G'.Nonempty ∧
      -- Delta-set at κ0 regularity
      IsProductLikeRealDeltaSCSet δ κ0 (C_A * δ ^ (-(10 * q_K + θ_num))) B1 ∧
      IsProductLikeRealDeltaSCSet δ κ0 (C_A * δ ^ (-(10 * q_K + θ_num))) B2 ∧
      -- Size lower bounds
      ENat.toENNReal B1.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S1.encard ∧
      ENat.toENNReal B2.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S2.encard ∧
      -- V3 absolute size lower bounds (3^10 absorbed via qSizeLossV3)
      ENat.toENNReal B1.encard ≥ ENNReal.ofReal (δ ^ (-s + qSizeLossV3)) ∧
      ENat.toENNReal B2.encard ≥ ENNReal.ofReal (δ ^ (-s + qSizeLossV3)) ∧
      -- Graph density (q_graph = 22*q_K, positive exponent)
      ENat.toENNReal (dyadicCoveringNumber δ G') ≥
        ENNReal.ofReal (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) *
          Nreal δ B1 * Nreal δ B2 ∧
      -- Full sector ledger: all 4 bounds in B1 normalization
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B1 * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B1 * Nreal δ B1 ∧
      -- Full sector ledger: all 4 bounds in B2 normalization
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ K_sector_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ K_sector_B2 * Nreal δ B2 ∧
      -- Wrapper-ready real bounds (B1 normalization)
      0 < K_BSG ∧
      Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 ∧
      -- Wrapper-ready real bounds (B2 normalization)
      0 < K_BSG_B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG_B2 * Nreal δ B2 ∧
      -- V3 exponent tracking
      0 < K_BSG_all ∧
      K_BSG ≤ K_BSG_all ∧
      K_BSG_B2 ≤ K_BSG_all ∧
      ENNReal.ofReal K_BSG_all ≥ K_sector_B1 ∧
      ENNReal.ofReal K_BSG_all ≥ K_sector_B2 ∧
      K_BSG_all ≤ δ ^ (-qDiffV3) := by
  /- Step 1: Set up K = δ^{-q_K} -/
  set K : ℝ := δ ^ (-q_K) with hK_def
  have hδqK_pos : 0 < δ ^ q_K := by positivity
  have hδqK_lt_one : δ ^ q_K < 1 := Real.rpow_lt_one (by linarith) hδ_lt_one (by linarith)
  have hK_gt_one : 1 < K := by
    rw [hK_def]
    have h_eq : δ ^ (-q_K) = (δ ^ q_K)⁻¹ := Real.rpow_neg (by linarith) q_K
    rw [h_eq]
    have h_inv : (δ ^ q_K)⁻¹ > 1 := by
      have h : (δ ^ q_K)⁻¹ = 1 / δ ^ q_K := by field_simp
      rw [h]
      exact one_lt_one_div hδqK_pos hδqK_lt_one
    exact h_inv
  have hK_pos : 0 < K := by linarith

  /- Step 2: Graph conversion Gamma → G : Set (ℝ × ℝ) -/
  let e2p : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun p => (p 0, p 1)
  let G : Set (ℝ × ℝ) := e2p '' Gamma
  have hG_sub : G ⊆ Set.prod S1 S2 := by
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    have h : p 0 ∈ S1 ∧ p 1 ∈ S2 := hGamma_sub p hp
    exact ⟨h.1, h.2⟩
  have hG_fin : G.Finite := hGamma_fin.image e2p
  have hG_bdd : IsBounded G := hG_fin.isBounded
  have hS1_bdd : IsBounded S1 := hS1_fin.isBounded
  have hS2_bdd : IsBounded S2 := hS2_fin.isBounded

  have h_graph_eq : graphToPlane G = Gamma := by
    ext p
    simp only [graphToPlane, Set.mem_image]
    constructor
    · rintro ⟨z, hz, h_eq⟩
      rcases hz with ⟨q, hq, rfl⟩
      have h_rt : (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i : Fin 2 => if i = 0 then q 0 else q 1) = q := by
        ext i; fin_cases i <;> simp
      rw [h_rt] at h_eq
      rw [← h_eq]; exact hq
    · intro hp
      refine ⟨e2p p, ⟨p, hp, rfl⟩, ?_⟩
      ext i; fin_cases i <;> simp [e2p]

  have h_sumset_eq : DiscretizedBSG.restrictedSumSet G =
      Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma := by
    ext x
    simp only [DiscretizedBSG.restrictedSumSet, Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨p, hp, rfl⟩
      exact ⟨p, hp, by ring⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨e2p p, ⟨p, hp, rfl⟩, by ring⟩

  /- Step 3: BSG corollary hypotheses -/
  have h_density_bsg : Nplane δ (graphToPlane G) ≥
      ENNReal.ofReal (1 / K) * Nreal δ S1 * Nreal δ S2 := by
    have h_main : Nplane δ (graphToPlane G) = ENat.toENNReal (dyadicCoveringNumber δ Gamma) := by
      rw [h_graph_eq] <;> rfl
    rw [h_main]
    have h1 : (1 / K : ℝ) = δ ^ q_K := by
      rw [hK_def]
      have h2 : δ ^ (-q_K) = (δ ^ q_K)⁻¹ := Real.rpow_neg (by linarith) q_K
      rw [h2]
      field_simp [hδqK_pos.ne'] <;> ring
    rw [h1]
    have h2 : ENNReal.ofReal (δ ^ q_K) ≤ ENNReal.ofReal c_dense := by
      gcongr <;> linarith
    calc ENat.toENNReal (dyadicCoveringNumber δ Gamma)
      ≥ ENNReal.ofReal c_dense * Nreal δ S1 * Nreal δ S2 := hGamma_dense
    _ ≥ ENNReal.ofReal (δ ^ q_K) * Nreal δ S1 * Nreal δ S2 := by gcongr

  have h_sumset_bsg : Nreal δ (DiscretizedBSG.restrictedSumSet G) ≤
      ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)) := by
    rw [h_sumset_eq]
    have h1 : ENNReal.ofReal C_sum ≤ ENNReal.ofReal K := by
      have hC_sum_le_K : C_sum ≤ K := by
        rw [hK_def] <;> exact hC_sum_le
      gcongr <;> exact hC_sum_le_K
    calc Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma)
      ≤ ENNReal.ofReal C_sum * ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)) := h_sumset
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)) := by gcongr

  /- Step 4: Apply bsg_corollary -/
  rcases bsg_corollary hδ_pos hS1_bdd hS2_bdd hG_bdd hG_sub hK_gt_one h_density_bsg h_sumset_bsg
    with ⟨A1', A2', hA1'_sub, hA2'_sub, h_ret1', h_ret2', h_sum_bound', h_graph_density'⟩

  let B1 := A1'
  let B2 := A2'
  let G' := graphToPlane (G ∩ Set.prod B1 B2)

  have hB1_sub_S1 : B1 ⊆ S1 := hA1'_sub
  have hB2_sub_S2 : B2 ⊆ S2 := hA2'_sub
  have hB1_bdd : IsBounded B1 := hS1_bdd.subset hB1_sub_S1
  have hB2_bdd : IsBounded B2 := hS2_bdd.subset hB2_sub_S2
  have hB1_nonempty : B1.Nonempty := by
    by_cases h : A1'.Nonempty
    · exact h
    · have h_empty : A1' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have h_pos : 0 < Nreal δ S1 := nreal_pos hδ_pos hS1_bdd hS1_nonempty
      have h_cpos : 0 < ENNReal.ofReal (1 / (K ^ 10 * (3 : ℝ) ^ 10)) * Nreal δ S1 := by positivity
      have hN_empty : Nreal δ A1' = 0 := by
        rw [h_empty]
        exact nreal_empty
      have h_le : ENNReal.ofReal (1 / (K ^ 10 * (3 : ℝ) ^ 10)) * Nreal δ S1 ≤ Nreal δ A1' := h_ret1'
      rw [hN_empty] at h_le
      have h_eq : ENNReal.ofReal (1 / (K ^ 10 * (3 : ℝ) ^ 10)) * Nreal δ S1 = 0 := by simpa using h_le
      exact False.elim (h_cpos.ne' h_eq)
  have hB2_nonempty : B2.Nonempty := by
    by_cases h : A2'.Nonempty
    · exact h
    · have h_empty : A2' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have h_pos : 0 < Nreal δ S2 := nreal_pos hδ_pos hS2_bdd hS2_nonempty
      have h_cpos : 0 < ENNReal.ofReal (1 / (K ^ 10 * (3 : ℝ) ^ 10)) * Nreal δ S2 := by positivity
      have hN_empty : Nreal δ A2' = 0 := by
        rw [h_empty]
        exact nreal_empty
      have h_le : ENNReal.ofReal (1 / (K ^ 10 * (3 : ℝ) ^ 10)) * Nreal δ S2 ≤ Nreal δ A2' := h_ret2'
      rw [hN_empty] at h_le
      have h_eq : ENNReal.ofReal (1 / (K ^ 10 * (3 : ℝ) ^ 10)) * Nreal δ S2 = 0 := by simpa using h_le
      exact False.elim (h_cpos.ne' h_eq)
  have hB1_grid : B1 ⊆ productLikeIntegerGrid δ := by
    intro x hx; exact hS1_grid (hB1_sub_S1 hx)
  have hB2_grid : B2 ⊆ productLikeIntegerGrid δ := by
    intro x hx; exact hS2_grid (hB2_sub_S2 hx)

  /- Step 5: Call bsg_to_wrapper_bounds for full ledger -/
  set C_bsg : ENNReal := ENNReal.ofReal (2 ^ 13 * (3 : ℝ) ^ 10 * K ^ 10) with hC_bsg_def
  set c_ret_enn : ENNReal := ENNReal.ofReal (1 / (K ^ 10 * (3 : ℝ) ^ 10)) with hc_ret_enn_def
  set c_graph_enn : ENNReal := ENNReal.ofReal (1 / (16 * K ^ 22 * (3 : ℝ) ^ 22)) with hc_graph_enn_def

  have hC_bsg_ne_top : C_bsg ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc_ret_enn_ne_top : c_ret_enn ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc_ret_enn_pos : 0 < c_ret_enn := by positivity
  have hC_bsg_pos : 0 < C_bsg := by positivity
  have hC_bsg_ge_one : 1 ≤ C_bsg := by
    rw [hC_bsg_def]
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ 13 * (3 : ℝ) ^ 10 * K ^ 10 := by
      have hK10 : 1 ≤ K ^ 10 := by
        have h1 : 1 ≤ K := by linarith
        have h2 : ∀ n : ℕ, 1 ≤ K ^ n := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
            have hK : 1 ≤ K := by linarith
            calc 1
              ≤ K ^ n := ih
            _ ≤ K ^ n * K := by exact le_mul_of_one_le_right (by positivity) hK
            _ = K ^ (n + 1) := by simp [pow_succ]
        exact h2 10
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) 13,
        pow_pos (show (0 : ℝ) < 3 by norm_num) 10]
    exact ENNReal.one_le_ofReal.mpr h
  have hK10_gt_one : 1 < K ^ 10 := by
    have h : 1 < K := hK_gt_one
    have h_pos : 0 < K := by linarith
    have h5 : K ^ 10 > K ^ 1 := by gcongr <;> norm_num
    have h6 : K ^ 1 = K := by ring
    rw [h6] at h5
    linarith
  have h310_gt_one : 1 < (3 : ℝ) ^ 10 := by norm_num
  have h_prod_gt_one : 1 < K ^ 10 * (3 : ℝ) ^ 10 := by
    have h4 : 1 < (3 : ℝ) ^ 10 := by norm_num
    have h5 : 0 < K ^ 10 := by positivity
    have h6 : 0 < (3 : ℝ) ^ 10 := by positivity
    nlinarith
  have hc_ret_enn_le_one : c_ret_enn ≤ 1 := by
    have h : (1 / (K ^ 10 * (3 : ℝ) ^ 10)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith
    exact ENNReal.ofReal_le_one.mpr h

  have h_ret1 : c_ret_enn * Nreal δ S1 ≤ Nreal δ B1 := by
    simpa [c_ret_enn] using h_ret1'
  have h_ret2 : c_ret_enn * Nreal δ S2 ≤ Nreal δ B2 := by
    simpa [c_ret_enn] using h_ret2'

  have h_sum_bsg : Nreal δ (Set.image2 (· + ·) B1 B2) ≤
      C_bsg * ENNReal.ofReal (Real.sqrt ((Nreal δ S1).toReal * (Nreal δ S2).toReal)) := by
    simpa [C_bsg] using h_sum_bound'

  have h_main := @ProductLikeIncidence.bsg_to_wrapper_bounds δ hδ_pos S1 S2 B1 B2
    hS1_bdd hS2_bdd hB1_bdd hB2_bdd hB1_nonempty hB2_nonempty
    hB1_grid hB2_grid hB1_sub_S1 hB2_sub_S2
    C_bsg c_ret_enn K_A
    hC_bsg_ne_top hc_ret_enn_ne_top hc_ret_enn_pos hC_bsg_pos
    hK_A_ne_top hK_A_ge_one hC_bsg_ge_one hc_ret_enn_le_one
    h_ret1 h_ret2 h_sum_bsg hS1_le_S2 hS2_le_S1
  rcases h_main with ⟨K_eff, K_ratio, K_sector, K_sector_B1, K_sector_B2, K_BSG_B1, K_BSG_B2, K_BSG_all, h_props⟩
  rcases h_props with ⟨hK_eff_def, hK_ratio_def, h_diff1_B1, h_diff2_B1, h_diff3_B1, h_diff4_B1,
    hK_sector_ne_top, hK_sector_ne_zero,
    h_d1_B1, h_d2_B1, h_d3_B1, h_d1_B2, h_d2_B2, h_d3_B2,
    hK_BSG_B1_pos, h_r1, h_r2, h_r3,
    hK_BSG_B2_pos, h_r4, h_r5, h_r6,
    hK_BSG_all_pos, h_all_ge_B1, h_all_ge_B2, hK_BSG_all_B1, hK_BSG_all_B2, hK_BSG_all_le⟩

  let K_BSG : ℝ := K_BSG_B1
  have h_diff1 : Nreal δ (Set.image2 (· - ·) B1 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 := h_r1
  have h_diff2 : Nreal δ (Set.image2 (· - ·) B2 B1) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 := h_r2
  have h_diff3 : Nreal δ (Set.image2 (· + ·) B1 B2) ≤ ENNReal.ofReal K_BSG * Nreal δ B1 := h_r3

  /- Step 6: Delta-set properties (weaken constant, then exponent s→κ0) -/
  set C_weak : ℝ := C_A * δ ^ (-(10 * q_K + θ_num)) with hC_weak_def
  set c_ret_real : ℝ := 1 / (K ^ 10 * (3 : ℝ) ^ 10) with hc_ret_real_def
  have hc_ret_real_pos : 0 < c_ret_real := by positivity

  have hK10_eq : K ^ 10 = δ ^ (-10 * q_K) := by
    rw [hK_def]
    calc (δ ^ (-q_K)) ^ 10
      = (δ ^ (-q_K)) ^ (10 : ℝ) := by norm_cast
    _ = δ ^ ((-q_K) * (10 : ℝ)) := by rw [← Real.rpow_mul (by linarith)]
    _ = δ ^ (-10 * q_K) := by rw [show (-q_K) * (10 : ℝ) = -10 * q_K by ring]

  have h_const_le : C_A / c_ret_real ≤ C_weak := by
    have h1 : C_A / c_ret_real = C_A * (K ^ 10 * (3 : ℝ) ^ 10) := by
      rw [hc_ret_real_def]
      have h_pos : 0 < K ^ 10 * (3 : ℝ) ^ 10 := by positivity
      field_simp [h_pos.ne'] <;> ring
    rw [h1, hC_weak_def, hK10_eq]
    have h7 : 0 < δ ^ θ_num := by positivity
    have h8 : (3 : ℝ) ^ 10 * δ ^ θ_num ≤ 1 := by
      calc (3 : ℝ) ^ 10 * δ ^ θ_num
        ≤ (3 : ℝ) ^ 10 * (1 / (3 ^ 10 : ℝ)) := by gcongr
      _ = 1 := by field_simp <;> ring
    have h9 : (3 : ℝ) ^ 10 ≤ 1 / δ ^ θ_num := by
      calc (3 : ℝ) ^ 10
        = ((3 : ℝ) ^ 10 * δ ^ θ_num) / δ ^ θ_num := by field_simp [h7.ne'] <;> ring
      _ ≤ 1 / δ ^ θ_num := by gcongr
    have h10 : δ ^ (-θ_num) = 1 / δ ^ θ_num := by
      have h11 : δ ^ (-θ_num) = (δ ^ θ_num)⁻¹ := Real.rpow_neg (by linarith) θ_num
      rw [h11] <;> field_simp
    have h5 : (3 : ℝ) ^ 10 ≤ δ ^ (-θ_num) := by
      rw [h10] <;> exact h9
    have h12 : δ ^ (-10 * q_K) * (3 : ℝ) ^ 10 ≤ δ ^ (-10 * q_K) * δ ^ (-θ_num) := by gcongr
    have h13 : δ ^ (-10 * q_K) * δ ^ (-θ_num) = δ ^ (-(10 * q_K + θ_num)) := by
      have h_sum : δ ^ (-10 * q_K) * δ ^ (-θ_num) = δ ^ ((-10 * q_K) + (-θ_num)) := by
        rw [← Real.rpow_add (by linarith)]
      rw [h_sum]
      have h_eq : (-10 * q_K) + (-θ_num) = -(10 * q_K + θ_num) := by ring
      rw [h_eq]
    have h14 : δ ^ (-10 * q_K) * (3 : ℝ) ^ 10 ≤ δ ^ (-(10 * q_K + θ_num)) := by
      calc δ ^ (-10 * q_K) * (3 : ℝ) ^ 10
        ≤ δ ^ (-10 * q_K) * δ ^ (-θ_num) := h12
      _ = δ ^ (-(10 * q_K + θ_num)) := h13
    gcongr

  have h_fraction1 : ENNReal.ofReal c_ret_real * Nreal δ S1 ≤ Nreal δ B1 := by
    have h_eq : c_ret_enn = ENNReal.ofReal c_ret_real := by
      simp [c_ret_enn, c_ret_real]
    rw [h_eq] at h_ret1
    exact h_ret1

  have hS1_delta' : IsRealDeltaSet δ κ0 C_A S1 := by
    simpa [IsRealDeltaSet, IsProductLikeRealDeltaSCSet, realLineCopy, productLikeRealLineCopy] using hS1_delta
  have hS2_delta' : IsRealDeltaSet δ κ0 C_A S2 := by
    simpa [IsRealDeltaSet, IsProductLikeRealDeltaSCSet, realLineCopy, productLikeRealLineCopy] using hS2_delta

  have hB1_delta_kappa0 : IsProductLikeRealDeltaSCSet δ κ0 (C_A / c_ret_real) B1 :=
    robust_projection.is_real_delta_set_of_subset_fraction hB1_sub_S1 hS1_delta' hc_ret_real_pos h_fraction1

  have hB1_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 C_weak B1 :=
    weaken_delta_set_constant hB1_delta_kappa0 h_const_le

  have h_fraction2 : ENNReal.ofReal c_ret_real * Nreal δ S2 ≤ Nreal δ B2 := by
    have h_eq : c_ret_enn = ENNReal.ofReal c_ret_real := by
      simp [c_ret_enn, c_ret_real]
    rw [h_eq] at h_ret2
    exact h_ret2

  have hB2_delta_kappa0 : IsProductLikeRealDeltaSCSet δ κ0 (C_A / c_ret_real) B2 :=
    robust_projection.is_real_delta_set_of_subset_fraction hB2_sub_S2 hS2_delta' hc_ret_real_pos h_fraction2

  have hB2_delta_kappa : IsProductLikeRealDeltaSCSet δ κ0 C_weak B2 :=
    weaken_delta_set_constant hB2_delta_kappa0 h_const_le

  /- Step 7: Size bounds in encard form -/
  have hB1_fin : B1.Finite := hS1_fin.subset hB1_sub_S1
  have hB2_fin : B2.Finite := hS2_fin.subset hB2_sub_S2

  let T1 := hS1_fin.toFinset
  let T2 := hS2_fin.toFinset
  let TB1 := hB1_fin.toFinset
  let TB2 := hB2_fin.toFinset

  have hT1 : (T1 : Set ℝ) = S1 := by simp [T1]
  have hT2 : (T2 : Set ℝ) = S2 := by simp [T2]
  have hTB1 : (TB1 : Set ℝ) = B1 := by simp [TB1]
  have hTB2 : (TB2 : Set ℝ) = B2 := by simp [TB2]

  have h_sep1 : ∀ p ∈ T1, ∀ q ∈ T1, p ≠ q → dist p q ≥ δ := by
    intro p hp q hq hneq
    have h_pS1 : p ∈ S1 := by rw [← hT1] <;> exact hp
    have h_qS1 : q ∈ S1 := by rw [← hT1] <;> exact hq
    have h : |p - q| ≥ δ := hS1_sep p h_pS1 q h_qS1 hneq
    simpa [dist_eq_norm, Real.norm_eq_abs] using h
  have h_sep2 : ∀ p ∈ T2, ∀ q ∈ T2, p ≠ q → dist p q ≥ δ := by
    intro p hp q hq hneq
    have h_pS2 : p ∈ S2 := by rw [← hT2] <;> exact hp
    have h_qS2 : q ∈ S2 := by rw [← hT2] <;> exact hq
    have h : |p - q| ≥ δ := hS2_sep p h_pS2 q h_qS2 hneq
    simpa [dist_eq_norm, Real.norm_eq_abs] using h

  have hN_S1_eq : Nreal δ S1 = ENat.toENNReal S1.encard := by
    have h_main : dyadicCoveringNumber δ (realLineCopy (T1 : Set ℝ)) = ↑T1.card :=
      robust_projection.covering_number_eq_card_of_separated hδ_pos h_sep1
    have h_eq1 : realLineCopy S1 = realLineCopy (T1 : Set ℝ) := by
      ext x; simp [realLineCopy, hT1]
    have h_encard : S1.encard = ↑T1.card := by
      have h : S1.encard = (T1 : Set ℝ).encard := by rw [hT1]
      rw [h]; simp
    have h_unfold : Nreal δ S1 = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy S1)) := by rfl
    rw [h_unfold, h_eq1, h_main, h_encard]
  have hN_S2_eq : Nreal δ S2 = ENat.toENNReal S2.encard := by
    have h_main : dyadicCoveringNumber δ (realLineCopy (T2 : Set ℝ)) = ↑T2.card :=
      robust_projection.covering_number_eq_card_of_separated hδ_pos h_sep2
    have h_eq1 : realLineCopy S2 = realLineCopy (T2 : Set ℝ) := by
      ext x; simp [realLineCopy, hT2]
    have h_encard : S2.encard = ↑T2.card := by
      have h : S2.encard = (T2 : Set ℝ).encard := by rw [hT2]
      rw [h]; simp
    have h_unfold : Nreal δ S2 = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy S2)) := by rfl
    rw [h_unfold, h_eq1, h_main, h_encard]

  have h_sepB1 : ∀ p ∈ TB1, ∀ q ∈ TB1, p ≠ q → dist p q ≥ δ := by
    intro p hp q hq hneq
    have h_pB1 : p ∈ B1 := by rw [← hTB1] <;> exact hp
    have h_qB1 : q ∈ B1 := by rw [← hTB1] <;> exact hq
    have h : |p - q| ≥ δ := hS1_sep p (hB1_sub_S1 h_pB1) q (hB1_sub_S1 h_qB1) hneq
    simpa [dist_eq_norm, Real.norm_eq_abs] using h
  have h_sepB2 : ∀ p ∈ TB2, ∀ q ∈ TB2, p ≠ q → dist p q ≥ δ := by
    intro p hp q hq hneq
    have h_pB2 : p ∈ B2 := by rw [← hTB2] <;> exact hp
    have h_qB2 : q ∈ B2 := by rw [← hTB2] <;> exact hq
    have h : |p - q| ≥ δ := hS2_sep p (hB2_sub_S2 h_pB2) q (hB2_sub_S2 h_qB2) hneq
    simpa [dist_eq_norm, Real.norm_eq_abs] using h

  have hN_B1_eq : Nreal δ B1 = ENat.toENNReal B1.encard := by
    have h_main : dyadicCoveringNumber δ (realLineCopy (TB1 : Set ℝ)) = ↑TB1.card :=
      robust_projection.covering_number_eq_card_of_separated hδ_pos h_sepB1
    have h_eq1 : realLineCopy B1 = realLineCopy (TB1 : Set ℝ) := by
      ext x; simp [realLineCopy, hTB1]
    have h_encard : B1.encard = ↑TB1.card := by
      have h : B1.encard = (TB1 : Set ℝ).encard := by rw [hTB1]
      rw [h]; simp
    have h_unfold : Nreal δ B1 = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B1)) := by rfl
    rw [h_unfold, h_eq1, h_main, h_encard]
  have hN_B2_eq : Nreal δ B2 = ENat.toENNReal B2.encard := by
    have h_main : dyadicCoveringNumber δ (realLineCopy (TB2 : Set ℝ)) = ↑TB2.card :=
      robust_projection.covering_number_eq_card_of_separated hδ_pos h_sepB2
    have h_eq1 : realLineCopy B2 = realLineCopy (TB2 : Set ℝ) := by
      ext x; simp [realLineCopy, hTB2]
    have h_encard : B2.encard = ↑TB2.card := by
      have h : B2.encard = (TB2 : Set ℝ).encard := by rw [hTB2]
      rw [h]; simp
    have h_unfold : Nreal δ B2 = ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy B2)) := by rfl
    rw [h_unfold, h_eq1, h_main, h_encard]

  have h_ret1_real : ENat.toENNReal B1.encard ≥
      ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S1.encard := by
    have h1 : (1 / (K ^ 10 * (3 : ℝ) ^ 10)) = δ ^ (10 * q_K) / (3 ^ 10 : ℝ) := by
      rw [hK10_eq]
      have h_pos : 0 < δ ^ (10 * q_K) := by positivity
      have h2 : δ ^ (-10 * q_K) = (δ ^ (10 * q_K))⁻¹ := by
        have h3 : (-10 * q_K) = -(10 * q_K) := by ring
        rw [h3]
        exact Real.rpow_neg (by linarith) (10 * q_K)
      rw [h2]
      field_simp [h_pos.ne'] <;> ring
    have h_crett : c_ret_enn = ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) := by
      simp [c_ret_enn, h1]
    have h_ret1'_rw : c_ret_enn * Nreal δ S1 ≤ Nreal δ B1 := by
      simpa [B1] using h_ret1'
    rw [h_crett] at h_ret1'_rw
    rw [← hN_B1_eq, ← hN_S1_eq]
    exact h_ret1'_rw
  have h_ret2_real : ENat.toENNReal B2.encard ≥
      ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S2.encard := by
    have h1 : (1 / (K ^ 10 * (3 : ℝ) ^ 10)) = δ ^ (10 * q_K) / (3 ^ 10 : ℝ) := by
      rw [hK10_eq]
      have h_pos : 0 < δ ^ (10 * q_K) := by positivity
      have h2 : δ ^ (-10 * q_K) = (δ ^ (10 * q_K))⁻¹ := by
        have h3 : (-10 * q_K) = -(10 * q_K) := by ring
        rw [h3]
        exact Real.rpow_neg (by linarith) (10 * q_K)
      rw [h2]
      field_simp [h_pos.ne'] <;> ring
    have h_crett : c_ret_enn = ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) := by
      simp [c_ret_enn, h1]
    have h_ret2'_rw : c_ret_enn * Nreal δ S2 ≤ Nreal δ B2 := by
      simpa [B2] using h_ret2'
    rw [h_crett] at h_ret2'_rw
    rw [← hN_B2_eq, ← hN_S2_eq]
    exact h_ret2'_rw

  /- Step 8: Graph properties -/
  have hG'_sub_Gamma : G' ⊆ Gamma := by
    intro p hp
    have h1 : G' ⊆ graphToPlane G := by
      intro x hx
      rcases hx with ⟨z, hz, rfl⟩
      exact ⟨z, hz.1, rfl⟩
    have h2 : p ∈ graphToPlane G := h1 hp
    rw [h_graph_eq] at h2
    exact h2
  have hG'_sub_prod : ∀ p ∈ G', p 0 ∈ B1 ∧ p 1 ∈ B2 := by
    intro p hp
    rcases hp with ⟨z, hz, rfl⟩
    exact ⟨hz.2.1, hz.2.2⟩
  have hG'_grid : ∀ p ∈ G', ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ) := by
    intro p hp i
    have h_pGamma : p ∈ Gamma := hG'_sub_Gamma hp
    exact hGamma_grid p h_pGamma i

  have hN_B1_pos : 0 < Nreal δ B1 := nreal_pos hδ_pos hB1_bdd hB1_nonempty
  have hN_B2_pos : 0 < Nreal δ B2 := nreal_pos hδ_pos hB2_bdd hB2_nonempty

  have hG'_nonempty : G'.Nonempty := by
    have h5 : ENat.toENNReal (dyadicCoveringNumber δ G') ≥
        c_graph_enn * Nreal δ S1 * Nreal δ S2 := h_graph_density'
    have h6 : 0 < Nreal δ S1 := nreal_pos hδ_pos hS1_bdd hS1_nonempty
    have h7 : 0 < Nreal δ S2 := nreal_pos hδ_pos hS2_bdd hS2_nonempty
    have h8 : 0 < c_graph_enn := by positivity
    have h9 : 0 < c_graph_enn * Nreal δ S1 * Nreal δ S2 := by positivity
    have h4 : 0 < ENat.toENNReal (dyadicCoveringNumber δ G') := lt_of_lt_of_le h9 h5
    by_contra h
    have h_empty : G' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h10 : ENat.toENNReal (dyadicCoveringNumber δ G') = 0 := by
      rw [h_empty]
      simp [dyadicCoveringNumber, dyadicCubesMeeting]
    rw [h10] at h4
    exact False.elim (lt_irrefl 0 h4)

  have h_cgraph_eq : c_graph_enn = ENNReal.ofReal (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) := by
    have hK22_eq : K ^ 22 = δ ^ (-22 * q_K) := by
      rw [hK_def]
      calc (δ ^ (-q_K)) ^ 22
        = (δ ^ (-q_K)) ^ (22 : ℝ) := by norm_cast
      _ = δ ^ ((-q_K) * (22 : ℝ)) := by rw [← Real.rpow_mul (by linarith)]
      _ = δ ^ (-22 * q_K) := by ring_nf
    have h_pos : 0 < δ ^ (22 * q_K) := by positivity
    have h_inv : δ ^ (-22 * q_K) = (δ ^ (22 * q_K))⁻¹ := by
      have h3 : (-22 * q_K) = -(22 * q_K) := by ring
      rw [h3]
      exact Real.rpow_neg (by linarith) (22 * q_K)
    have h_main : c_graph_enn = ENNReal.ofReal (1 / (16 * K ^ 22 * (3 : ℝ) ^ 22)) := by
      simp [c_graph_enn]
    rw [h_main]
    have h_eq : (1 / (16 * K ^ 22 * (3 : ℝ) ^ 22)) = δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ)) := by
      rw [hK22_eq, h_inv]
      field_simp [h_pos.ne'] <;> ring
    rw [h_eq]

  have hN_B1_le_S1 : Nreal δ B1 ≤ Nreal δ S1 := by
    have h1 : realLineCopy B1 ⊆ realLineCopy S1 := by
      intro x hx; simpa [realLineCopy] using hB1_sub_S1 (by simpa [realLineCopy] using hx)
    have h2 : dyadicCubesMeeting δ (realLineCopy B1) ⊆ dyadicCubesMeeting δ (realLineCopy S1) := by
      intro Q hQ
      rcases hQ with ⟨hQ1, hQ2⟩
      have h3 : Q ∩ realLineCopy B1 ⊆ Q ∩ realLineCopy S1 := Set.inter_subset_inter_right Q h1
      exact ⟨hQ1, Set.Nonempty.mono h3 hQ2⟩
    have h3 : (dyadicCubesMeeting δ (realLineCopy B1)).encard ≤ (dyadicCubesMeeting δ (realLineCopy S1)).encard :=
      Set.encard_mono h2
    exact ENat.toENNReal_mono h3
  have hN_B2_le_S2 : Nreal δ B2 ≤ Nreal δ S2 := by
    have h1 : realLineCopy B2 ⊆ realLineCopy S2 := by
      intro x hx; simpa [realLineCopy] using hB2_sub_S2 (by simpa [realLineCopy] using hx)
    have h2 : dyadicCubesMeeting δ (realLineCopy B2) ⊆ dyadicCubesMeeting δ (realLineCopy S2) := by
      intro Q hQ
      rcases hQ with ⟨hQ1, hQ2⟩
      have h3 : Q ∩ realLineCopy B2 ⊆ Q ∩ realLineCopy S2 := Set.inter_subset_inter_right Q h1
      exact ⟨hQ1, Set.Nonempty.mono h3 hQ2⟩
    have h3 : (dyadicCubesMeeting δ (realLineCopy B2)).encard ≤ (dyadicCubesMeeting δ (realLineCopy S2)).encard :=
      Set.encard_mono h2
    exact ENat.toENNReal_mono h3

  have h_graph_density_final : ENat.toENNReal (dyadicCoveringNumber δ G') ≥
      ENNReal.ofReal (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * Nreal δ B1 * Nreal δ B2 := by
    have h_dens1 : ENat.toENNReal (dyadicCoveringNumber δ G') ≥
        c_graph_enn * Nreal δ S1 * Nreal δ S2 := h_graph_density'
    calc ENat.toENNReal (dyadicCoveringNumber δ G')
      ≥ c_graph_enn * Nreal δ S1 * Nreal δ S2 := h_dens1
    _ = ENNReal.ofReal (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * Nreal δ S1 * Nreal δ S2 := by
      rw [h_cgraph_eq]
    _ ≥ ENNReal.ofReal (δ ^ (22 * q_K) / (16 * (3 ^ 22 : ℝ))) * Nreal δ B1 * Nreal δ B2 := by gcongr

  /- Step 9b: V3 exponent tracking -/

  -- Explicit forms of K_eff and K_ratio
  have hK_eff_explicit : K_eff = ENNReal.ofReal ((2 : ℝ) ^ 13 * (3 : ℝ) ^ 20 * K ^ 20) := by
    have h_pos1 : 0 < (2 : ℝ) ^ 13 * (3 : ℝ) ^ 10 * K ^ 10 := by positivity
    have h_pos2 : 0 < (1 : ℝ) / (K ^ 10 * (3 : ℝ) ^ 10) := by positivity
    have h_div : C_bsg / c_ret_enn = ENNReal.ofReal ((2 : ℝ) ^ 13 * (3 : ℝ) ^ 20 * K ^ 20) := by
      rw [hC_bsg_def, hc_ret_enn_def]
      have h_eq : ENNReal.ofReal ((2 : ℝ) ^ 13 * (3 : ℝ) ^ 10 * K ^ 10) / ENNReal.ofReal ((1 : ℝ) / (K ^ 10 * (3 : ℝ) ^ 10)) =
          ENNReal.ofReal (((2 : ℝ) ^ 13 * (3 : ℝ) ^ 10 * K ^ 10) / ((1 : ℝ) / (K ^ 10 * (3 : ℝ) ^ 10))) := by
        exact (ENNReal.ofReal_div_of_pos h_pos2).symm
      rw [h_eq]
      have h_real : ((2 : ℝ) ^ 13 * (3 : ℝ) ^ 10 * K ^ 10) / ((1 : ℝ) / (K ^ 10 * (3 : ℝ) ^ 10)) =
          (2 : ℝ) ^ 13 * (3 : ℝ) ^ 20 * K ^ 20 := by
        field_simp [h_pos1.ne'] <;> ring
      rw [h_real]
    exact hK_eff_def.trans h_div

  have hK_ratio_explicit : K_ratio = K_A * ENNReal.ofReal (K ^ 10 * (3 : ℝ) ^ 10) := by
    have h_pos : 0 < (1 : ℝ) / (K ^ 10 * (3 : ℝ) ^ 10) := by positivity
    have h_div : K_A / c_ret_enn = K_A * ENNReal.ofReal (K ^ 10 * (3 : ℝ) ^ 10) := by
      rw [hc_ret_enn_def]
      have h_inv : (ENNReal.ofReal ((1 : ℝ) / (K ^ 10 * (3 : ℝ) ^ 10)))⁻¹ = ENNReal.ofReal (K ^ 10 * (3 : ℝ) ^ 10) := by
        have h_real_inv : ((1 : ℝ) / (K ^ 10 * (3 : ℝ) ^ 10))⁻¹ = K ^ 10 * (3 : ℝ) ^ 10 := by
          field_simp [h_pos.ne'] <;> ring
        rw [← ENNReal.ofReal_inv_of_pos h_pos, h_real_inv]
      rw [div_eq_mul_inv, h_inv] <;> ring
    rw [hK_ratio_def]
    exact h_div

  -- Main bound: 81 * K_eff^3 * K_ratio^2 ≤ ofReal(δ^(-qDiffV3))
  set a : ℝ := (2 : ℝ) ^ 13 * (3 : ℝ) ^ 20 * K ^ 20 with ha_def
  set b : ℝ := K ^ 10 * (3 : ℝ) ^ 10 with hb_def
  have ha_pos : 0 ≤ a := by positivity
  have hb_pos : 0 ≤ b := by positivity

  have hK_A2_le : K_A ^ 2 ≤ ENNReal.ofReal (δ ^ (-2 * qKA)) := by
    have h1 : K_A ≤ ENNReal.ofReal (δ ^ (-qKA)) := hK_A_le
    have h2 : K_A ^ 2 ≤ (ENNReal.ofReal (δ ^ (-qKA))) ^ 2 := by gcongr
    have h_pos4 : 0 ≤ δ ^ (-qKA) := by positivity
    have h3 : (ENNReal.ofReal (δ ^ (-qKA))) ^ 2 = ENNReal.ofReal ((δ ^ (-qKA)) ^ 2) := by
      rw [← ENNReal.ofReal_pow h_pos4 2]
    have h4 : (δ ^ (-qKA)) ^ 2 = δ ^ (-2 * qKA) := by
      have h5 : (δ ^ (-qKA)) ^ 2 = (δ ^ (-qKA)) ^ (2 : ℝ) := by norm_cast
      rw [h5]
      have h6 : (δ ^ (-qKA)) ^ (2 : ℝ) = δ ^ ((-qKA) * (2 : ℝ)) :=
        (Real.rpow_mul hδ_pos.le (-qKA) 2).symm
      rw [h6] <;> ring_nf
    rw [h3, h4] at h2
    exact h2

  have h_a3 : (ENNReal.ofReal a) ^ 3 = ENNReal.ofReal (a ^ 3) := by
    exact (ENNReal.ofReal_pow ha_pos 3).symm

  have h_b2 : (ENNReal.ofReal b) ^ 2 = ENNReal.ofReal (b ^ 2) := by
    exact (ENNReal.ofReal_pow hb_pos 2).symm

  have h_main_bound : 81 * K_eff ^ 3 * K_ratio ^ 2 ≤ ENNReal.ofReal (δ ^ (-qDiffV3)) := by
    rw [hK_eff_explicit, hK_ratio_explicit]
    have h_eq2 : (K_A * ENNReal.ofReal b) ^ 2 = K_A ^ 2 * (ENNReal.ofReal b) ^ 2 := by
      simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
    have h_prod : ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (δ ^ (-2 * qKA)) * ENNReal.ofReal (b ^ 2) =
        ENNReal.ofReal (a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2) := by
      have h_pos1 : 0 ≤ a ^ 3 := by positivity
      have h_pos2 : 0 ≤ δ ^ (-2 * qKA) := by positivity
      have h1 : ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (δ ^ (-2 * qKA)) =
          ENNReal.ofReal (a ^ 3 * (δ ^ (-2 * qKA))) := by
        rw [← ENNReal.ofReal_mul h_pos1]
      rw [h1]
      have h2 : ENNReal.ofReal (a ^ 3 * (δ ^ (-2 * qKA))) * ENNReal.ofReal (b ^ 2) =
          ENNReal.ofReal ((a ^ 3 * (δ ^ (-2 * qKA))) * b ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      rw [h2] <;> ring
    have h_real_eq : a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2 =
        (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * K ^ 80 * δ ^ (-2 * qKA) := by
      have h_a3 : a ^ 3 = (2 : ℝ) ^ 39 * (3 : ℝ) ^ 60 * K ^ 60 := by
        dsimp only [a]; ring
      have h_b2 : b ^ 2 = K ^ 20 * (3 : ℝ) ^ 20 := by
        dsimp only [b]; ring
      rw [h_a3, h_b2] <;> ring
    have hK80 : K ^ 80 = δ ^ (-80 * q_K) := by
      rw [hK_def]
      have h5 : (δ ^ (-q_K)) ^ 80 = (δ ^ (-q_K)) ^ (80 : ℝ) := by norm_cast
      rw [h5]
      have h6 : (δ ^ (-q_K)) ^ (80 : ℝ) = δ ^ ((-q_K) * (80 : ℝ)) :=
        (Real.rpow_mul hδ_pos.le (-q_K) 80).symm
      rw [h6] <;> ring_nf
    have h_final : (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 *
        δ ^ (-(80 * q_K + 2 * qKA)) ≤ δ ^ (-qDiffV3) := by
      have h6 : δ ^ (-qDiffV3) = δ ^ (-qAbsorb) * δ ^ (-(80 * q_K + 2 * qKA)) := by
        rw [hqDiffV3_eq]
        have h7 : -(80 * q_K + 2 * qKA + qAbsorb) = -qAbsorb + (-(80 * q_K + 2 * qKA)) := by ring
        rw [h7]
        exact Real.rpow_add hδ_pos (-qAbsorb) (-(80 * q_K + 2 * qKA))
      rw [h6]
      have h8 : 0 ≤ δ ^ (-(80 * q_K + 2 * qKA)) := by positivity
      exact mul_le_mul_of_nonneg_right h_absorb_KBSG h8
    have h81 : (81 : ENNReal) = ENNReal.ofReal (81 : ℝ) := by simp
    have h_step1 : (81 : ENNReal) * (ENNReal.ofReal a) ^ 3 * (K_A * ENNReal.ofReal b) ^ 2 =
        (81 : ENNReal) * ENNReal.ofReal (a ^ 3) * K_A ^ 2 * ENNReal.ofReal (b ^ 2) := by
      have h1 : (K_A * ENNReal.ofReal b) ^ 2 = K_A ^ 2 * (ENNReal.ofReal b) ^ 2 := h_eq2
      calc (81 : ENNReal) * (ENNReal.ofReal a) ^ 3 * (K_A * ENNReal.ofReal b) ^ 2
        = (81 : ENNReal) * (ENNReal.ofReal a) ^ 3 * (K_A ^ 2 * (ENNReal.ofReal b) ^ 2) := by rw [h1]
      _ = (81 : ENNReal) * (ENNReal.ofReal a) ^ 3 * K_A ^ 2 * (ENNReal.ofReal b) ^ 2 := by simp [mul_assoc]
      _ = (81 : ENNReal) * ENNReal.ofReal (a ^ 3) * K_A ^ 2 * (ENNReal.ofReal b) ^ 2 := by rw [h_a3]
      _ = (81 : ENNReal) * ENNReal.ofReal (a ^ 3) * K_A ^ 2 * ENNReal.ofReal (b ^ 2) := by rw [h_b2]
    have h_combine : (81 : ENNReal) * ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (δ ^ (-2 * qKA)) * ENNReal.ofReal (b ^ 2) =
        ENNReal.ofReal ((81 : ℝ) * a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2) := by
      rw [h81]
      have h_pos1 : 0 ≤ (81 : ℝ) := by positivity
      have h_pos2 : 0 ≤ a ^ 3 := by positivity
      have h_pos3 : 0 ≤ δ ^ (-2 * qKA) := by positivity
      have h_pos4 : 0 ≤ b ^ 2 := by positivity
      have h1 : ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (a ^ 3) = ENNReal.ofReal ((81 : ℝ) * a ^ 3) := by
        rw [← ENNReal.ofReal_mul h_pos1]
      have h2 : ENNReal.ofReal ((81 : ℝ) * a ^ 3) * ENNReal.ofReal (δ ^ (-2 * qKA)) = ENNReal.ofReal (((81 : ℝ) * a ^ 3) * (δ ^ (-2 * qKA))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      have h3 : ENNReal.ofReal (((81 : ℝ) * a ^ 3) * (δ ^ (-2 * qKA))) * ENNReal.ofReal (b ^ 2) = ENNReal.ofReal ((((81 : ℝ) * a ^ 3) * (δ ^ (-2 * qKA))) * b ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      calc ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (δ ^ (-2 * qKA)) * ENNReal.ofReal (b ^ 2)
        = (ENNReal.ofReal (81 : ℝ) * ENNReal.ofReal (a ^ 3)) * ENNReal.ofReal (δ ^ (-2 * qKA)) * ENNReal.ofReal (b ^ 2) := by simp [mul_assoc]
      _ = ENNReal.ofReal ((81 : ℝ) * a ^ 3) * ENNReal.ofReal (δ ^ (-2 * qKA)) * ENNReal.ofReal (b ^ 2) := by rw [h1]
      _ = ENNReal.ofReal (((81 : ℝ) * a ^ 3) * (δ ^ (-2 * qKA))) * ENNReal.ofReal (b ^ 2) := by rw [h2]
      _ = ENNReal.ofReal ((((81 : ℝ) * a ^ 3) * (δ ^ (-2 * qKA))) * b ^ 2) := by rw [h3]
      _ = ENNReal.ofReal ((81 : ℝ) * a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2) := by rfl
    have h_real_eq2 : (81 : ℝ) * a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2 =
        (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * K ^ 80 * δ ^ (-2 * qKA) := by
      have h : a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2 =
          (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * K ^ 80 * δ ^ (-2 * qKA) := h_real_eq
      calc (81 : ℝ) * a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2
        = (81 : ℝ) * (a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2) := by ring
      _ = (81 : ℝ) * ((2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * K ^ 80 * δ ^ (-2 * qKA)) := by rw [h]
      _ = (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * K ^ 80 * δ ^ (-2 * qKA) := by ring
    have h_exp_combine : δ ^ (-80 * q_K) * δ ^ (-2 * qKA) = δ ^ (-(80 * q_K + 2 * qKA)) := by
      have h : δ ^ (-80 * q_K + -2 * qKA) = δ ^ (-80 * q_K) * δ ^ (-2 * qKA) := Real.rpow_add hδ_pos (-80 * q_K) (-2 * qKA)
      have h_comm : (-80 * q_K + -2 * qKA : ℝ) = -(80 * q_K + 2 * qKA) := by ring
      have h4 : δ ^ (-(80 * q_K + 2 * qKA)) = δ ^ (-80 * q_K + -2 * qKA) := by rw [h_comm]
      exact h.symm.trans h4.symm
    have h_real_eq3 : (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * K ^ 80 * δ ^ (-2 * qKA) =
        (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * δ ^ (-(80 * q_K + 2 * qKA)) := by
      have h9 : K ^ 80 = δ ^ (-80 * q_K) := hK80
      rw [h9]
      have h10 : (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * δ ^ (-80 * q_K) * δ ^ (-2 * qKA) =
          (81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * (δ ^ (-80 * q_K) * δ ^ (-2 * qKA)) := by ring
      rw [h10, h_exp_combine] <;> ring
    calc
      (81 : ENNReal) * (ENNReal.ofReal a) ^ 3 * (K_A * ENNReal.ofReal b) ^ 2
        = (81 : ENNReal) * ENNReal.ofReal (a ^ 3) * K_A ^ 2 * ENNReal.ofReal (b ^ 2) := h_step1
      _ ≤ (81 : ENNReal) * ENNReal.ofReal (a ^ 3) * ENNReal.ofReal (δ ^ (-2 * qKA)) * ENNReal.ofReal (b ^ 2) := by
          gcongr
      _ = ENNReal.ofReal ((81 : ℝ) * a ^ 3 * (δ ^ (-2 * qKA)) * b ^ 2) := h_combine
      _ = ENNReal.ofReal ((81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * K ^ 80 * δ ^ (-2 * qKA)) := by
          exact congr_arg ENNReal.ofReal h_real_eq2
      _ = ENNReal.ofReal ((81 : ℝ) * (2 : ℝ) ^ 39 * (3 : ℝ) ^ 80 * δ ^ (-(80 * q_K + 2 * qKA))) := by
          exact congr_arg ENNReal.ofReal h_real_eq3
      _ ≤ ENNReal.ofReal (δ ^ (-qDiffV3)) := by
          exact ENNReal.ofReal_le_ofReal h_final

  have hK_BSG_all_le_old := hK_BSG_all_le
  have hK_BSG_all_final : K_BSG_all ≤ δ ^ (-qDiffV3) := by
    have h1 : ENNReal.ofReal K_BSG_all ≤ 81 * K_eff ^ 3 * K_ratio ^ 2 := hK_BSG_all_le_old
    have h2 : ENNReal.ofReal K_BSG_all ≤ ENNReal.ofReal (δ ^ (-qDiffV3)) :=
      le_trans h1 h_main_bound
    have h_top1 : ENNReal.ofReal K_BSG_all ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_top2 : ENNReal.ofReal (δ ^ (-qDiffV3)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h3 : (ENNReal.ofReal K_BSG_all).toReal ≤ (ENNReal.ofReal (δ ^ (-qDiffV3))).toReal :=
      (ENNReal.toReal_le_toReal h_top1 h_top2).mpr h2
    have h4 : (ENNReal.ofReal K_BSG_all).toReal = K_BSG_all :=
      ENNReal.toReal_ofReal (by linarith [hK_BSG_all_pos])
    have h5 : (ENNReal.ofReal (δ ^ (-qDiffV3))).toReal = δ ^ (-qDiffV3) :=
      ENNReal.toReal_ofReal (by positivity)
    rw [h4, h5] at h3
    exact h3

  -- V3 absolute size bounds with 3^10 absorption
  have hB1_size : ENat.toENNReal B1.encard ≥ ENNReal.ofReal (δ ^ (-s + qSizeLossV3)) := by
    have h1 : ENat.toENNReal B1.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S1.encard := h_ret1_real
    have h2 : ENat.toENNReal B1.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
      calc ENat.toENNReal B1.encard
        ≥ ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S1.encard := h1
      _ ≥ ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
        gcongr
    have h3 : ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (δ ^ (-s + q_input)) =
        ENNReal.ofReal ((δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * δ ^ (-s + q_input)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h3] at h2
    have h4 : (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * δ ^ (-s + q_input) =
        δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ) := by
      have h5 : δ ^ (10 * q_K) * δ ^ (-s + q_input) = δ ^ (-s + q_input + 10 * q_K) := by
        have h_rpow := Real.rpow_add hδ_pos (10 * q_K) (-s + q_input)
        have h_comm : (10 * q_K + (-s + q_input) : ℝ) = -s + q_input + 10 * q_K := by ring
        rw [h_comm] at h_rpow
        exact h_rpow.symm
      have h6 : (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * δ ^ (-s + q_input) =
          (δ ^ (10 * q_K) * δ ^ (-s + q_input)) / (3 ^ 10 : ℝ) := by ring
      rw [h6, h5]
    rw [h4] at h2
    have h_absorb : δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ) ≥ δ ^ (-s + qSizeLossV3) := by
      have h_pos : 0 < δ ^ (-s + q_input + 10 * q_K) := by positivity
      have h6 : (1 : ℝ) / (3 ^ 10 : ℝ) ≥ δ ^ (qSizeLossV3 - q_input - 10 * q_K) := h_absorb_size
      have h7 : δ ^ (-s + q_input + 10 * q_K) * ((1 : ℝ) / (3 ^ 10 : ℝ)) ≥
          δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) :=
        mul_le_mul_of_nonneg_left h6 h_pos.le
      have h_exp : (-s + q_input + 10 * q_K) + (qSizeLossV3 - q_input - 10 * q_K) = -s + qSizeLossV3 := by ring
      have h8 : δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) =
          δ ^ (-s + qSizeLossV3) := by
        have h_rpow : δ ^ ((-s + q_input + 10 * q_K) + (qSizeLossV3 - q_input - 10 * q_K)) =
            δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) :=
          Real.rpow_add hδ_pos (-s + q_input + 10 * q_K) (qSizeLossV3 - q_input - 10 * q_K)
        have h_exp2 : (-s + q_input + 10 * q_K) + (qSizeLossV3 - q_input - 10 * q_K) = -s + qSizeLossV3 := h_exp
        rw [h_exp2] at h_rpow
        exact h_rpow.symm
      have h9 : δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ) =
          δ ^ (-s + q_input + 10 * q_K) * ((1 : ℝ) / (3 ^ 10 : ℝ)) := by ring
      calc
        δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ)
          = δ ^ (-s + q_input + 10 * q_K) * ((1 : ℝ) / (3 ^ 10 : ℝ)) := h9
        _ ≥ δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) := h7
        _ = δ ^ (-s + qSizeLossV3) := h8
    exact le_trans (ENNReal.ofReal_le_ofReal h_absorb) h2

  have hB2_size : ENat.toENNReal B2.encard ≥ ENNReal.ofReal (δ ^ (-s + qSizeLossV3)) := by
    have h1 : ENat.toENNReal B2.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S2.encard := h_ret2_real
    have h2 : ENat.toENNReal B2.encard ≥
        ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
      calc ENat.toENNReal B2.encard
        ≥ ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENat.toENNReal S2.encard := h1
      _ ≥ ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
        gcongr
    have h3 : ENNReal.ofReal (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * ENNReal.ofReal (δ ^ (-s + q_input)) =
        ENNReal.ofReal ((δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * δ ^ (-s + q_input)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h3] at h2
    have h4 : (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * δ ^ (-s + q_input) =
        δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ) := by
      have h5 : δ ^ (10 * q_K) * δ ^ (-s + q_input) = δ ^ (-s + q_input + 10 * q_K) := by
        have h_rpow := Real.rpow_add hδ_pos (10 * q_K) (-s + q_input)
        have h_comm : (10 * q_K + (-s + q_input) : ℝ) = -s + q_input + 10 * q_K := by ring
        rw [h_comm] at h_rpow
        exact h_rpow.symm
      have h6 : (δ ^ (10 * q_K) / (3 ^ 10 : ℝ)) * δ ^ (-s + q_input) =
          (δ ^ (10 * q_K) * δ ^ (-s + q_input)) / (3 ^ 10 : ℝ) := by ring
      rw [h6, h5]
    rw [h4] at h2
    have h_absorb : δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ) ≥ δ ^ (-s + qSizeLossV3) := by
      have h_pos : 0 < δ ^ (-s + q_input + 10 * q_K) := by positivity
      have h6 : (1 : ℝ) / (3 ^ 10 : ℝ) ≥ δ ^ (qSizeLossV3 - q_input - 10 * q_K) := h_absorb_size
      have h7 : δ ^ (-s + q_input + 10 * q_K) * ((1 : ℝ) / (3 ^ 10 : ℝ)) ≥
          δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) :=
        mul_le_mul_of_nonneg_left h6 h_pos.le
      have h_exp : (-s + q_input + 10 * q_K) + (qSizeLossV3 - q_input - 10 * q_K) = -s + qSizeLossV3 := by ring
      have h8 : δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) =
          δ ^ (-s + qSizeLossV3) := by
        have h_rpow : δ ^ ((-s + q_input + 10 * q_K) + (qSizeLossV3 - q_input - 10 * q_K)) =
            δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) :=
          Real.rpow_add hδ_pos (-s + q_input + 10 * q_K) (qSizeLossV3 - q_input - 10 * q_K)
        have h_exp2 : (-s + q_input + 10 * q_K) + (qSizeLossV3 - q_input - 10 * q_K) = -s + qSizeLossV3 := h_exp
        rw [h_exp2] at h_rpow
        exact h_rpow.symm
      have h9 : δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ) =
          δ ^ (-s + q_input + 10 * q_K) * ((1 : ℝ) / (3 ^ 10 : ℝ)) := by ring
      calc
        δ ^ (-s + q_input + 10 * q_K) / (3 ^ 10 : ℝ)
          = δ ^ (-s + q_input + 10 * q_K) * ((1 : ℝ) / (3 ^ 10 : ℝ)) := h9
        _ ≥ δ ^ (-s + q_input + 10 * q_K) * δ ^ (qSizeLossV3 - q_input - 10 * q_K) := h7
        _ = δ ^ (-s + qSizeLossV3) := h8
    exact le_trans (ENNReal.ofReal_le_ofReal h_absorb) h2

  /- Step 10: Extract full ledger -/
  exact ⟨B1, B2, G', K_BSG, K_BSG_B2, K_BSG_all, K_sector_B1, K_sector_B2,
    hB1_sub_S1, hB2_sub_S2, hG'_sub_Gamma,
    hG'_sub_prod, hG'_grid, hG'_nonempty,
    hB1_delta_kappa, hB2_delta_kappa,
    h_ret1_real, h_ret2_real,
    hB1_size, hB2_size,
    h_graph_density_final,
    -- B1 normalization ledger
    h_d1_B1, h_d2_B1, h_d3_B1,
    -- B2 normalization ledger
    h_d1_B2, h_d2_B2, h_d3_B2,
    -- Wrapper-ready real bounds
    hK_BSG_B1_pos, h_diff1, h_diff2, h_diff3,
    hK_BSG_B2_pos, h_r4, h_r5, h_r6,
    -- V3 exponent tracking
    hK_BSG_all_pos, h_all_ge_B1, h_all_ge_B2, hK_BSG_all_B1, hK_BSG_all_B2, hK_BSG_all_final⟩

end ProductLikeIncidence.ProductReduction
