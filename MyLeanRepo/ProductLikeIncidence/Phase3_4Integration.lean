module

/-
# Phase 3-4 Integration

Wires Phase 3 (rounding extraction) into Phase 4 (rounded dense graph).

## Result

`phase3_4_integration` — takes Phase 2 output (E3', μE3', energy bounds, Pbar)
and produces:
- Phase 3: round, S1, S2, E3'' (high-mass subset, every point rounds into S1×S2)
- Phase 4: Gamma ⊆ S1×S2 with density (c_dense/4) and third-projection bound

## Key design choice

The adapter `rounded_graph_adapter` requires `∀ p ∈ input, round(p 0) ∈ S1`.
Phase 3 only guarantees this for E3'' (mass ≥ 1/2), not all of E3'.
So we feed **E3''** into the adapter, not E3'. The density hypothesis
must be stated relative to Nplane(E3'').

## Whiteprint node
`phase3_4_integration`
-/

public import MyLeanRepo.ProductLikeIncidence.ProjectedRoundingExtraction
public import MyLeanRepo.ProductLikeIncidence.RoundingExtractionBridge
public import MyLeanRepo.ProductLikeIncidence.RoundedGraphAdapter
public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical Finset

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Integrate Phase 3 (rounding extraction) with Phase 4 (rounded dense graph).

Takes Phase 2 output and produces Gamma ⊆ S1×S2 with density and third-projection bound.

The density hypothesis `h_density_E3''` must be established from the overall
incidence/Pbar density bound, adjusted for the fact that E3'' has ≥ 1/2 the
mass of E3'. -/
lemma phase3_4_integration
    {δ κ0 C_extract L η : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    {E3' E3'' Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    (round : ℝ → ℝ)
    (hround_grid : ∀ x, round x ∈ productLikeIntegerGrid δ)
    (h_round_near : ∀ x, |x - round x| ≤ δ / 2)
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    (hS1_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract S1)
    (hS2_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract S2)
    {μE3' : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE3']
    (hE3''_sub : E3'' ⊆ E3')
    (hE3''_mass : μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ))
    (hE3''_round : ∀ p ∈ E3'', round (p 0) ∈ S1 ∧ round (p 1) ∈ S2)
    (hE3'_finite : E3'.Finite)
    (hE3'_sub_Pbar : E3' ⊆ Pbar)
    (hPbar_bounded : IsBounded Pbar)
    -- Density bound relative to E3'' (must be established upstream)
    (c_dense : ENNReal)
    (h_density_E3'' : c_dense * Nreal δ S1 * Nreal δ S2 ≤
      ENat.toENNReal (dyadicCoveringNumber δ E3''))
    -- Third projection bound for E3'
    (h_third_proj_E3' : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) :
    ∃ (Gamma : Set (EuclideanSpace ℝ (Fin 2))),
      -- Phase 4 outputs
      (∀ p ∈ Gamma, p 0 ∈ S1 ∧ p 1 ∈ S2) ∧
      (∀ p ∈ Gamma, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
      ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
        (c_dense / 4) * Nreal δ S1 * Nreal δ S2 ∧
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
        3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') ∧
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
        3 * (ENNReal.ofReal (δ ^ (-(L * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) ∧
      (∀ g ∈ Gamma, ∃ z ∈ E3'', g 0 = round (z 0) ∧ g 1 = round (z 1)) := by
  have hE3''_finite : E3''.Finite := hE3'_finite.subset hE3''_sub
  have hE3''_sub_Pbar : E3'' ⊆ Pbar := subset_trans hE3''_sub hE3'_sub_Pbar

  have hround_grid : ∀ x, round x ∈ productLikeIntegerGrid δ := hround_grid

  have hS1_contains : ∀ p ∈ E3'', round (p 0) ∈ S1 := by
    intro p hp
    exact (hE3''_round p hp).1
  have hS2_contains : ∀ p ∈ E3'', round (p 1) ∈ S2 := by
    intro p hp
    exact (hE3''_round p hp).2

  -- Third projection bound for E3'' follows from E3' by monotonicity
  have h_third_proj_E3'' : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3'') ≤
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') :=
    robust_projection_main.Nreal_mono_local (Set.image_mono hE3''_sub)

  have h_third_proj_final : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3'') ≤
      ENNReal.ofReal (δ ^ (-(L * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)) :=
    le_trans h_third_proj_E3'' h_third_proj_E3'

  -- Phase 4: rounded dense graph (feed E3'' into adapter)
  obtain ⟨Gamma, hGamma_sub, hGamma_grid, hGamma_density, hGamma_third1, hGamma_third2, hGamma_witness⟩ :=
    rounded_graph_adapter
      hδ_pos hδ_dyadic
      (E3' := E3'') (Pbar := Pbar)
      hE3''_sub_Pbar hE3''_finite hPbar_bounded
      (S1 := S1) (S2 := S2)
      hS1_grid hS2_grid
      round hround_grid h_round_near
      hS1_contains hS2_contains
      c_dense h_density_E3''
      h_third_proj_final

  -- Convert third-proj bound from E3'' to E3'
  have hGamma_third1' : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
      3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') :=
    calc _ ≤ 3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3'') := hGamma_third1
         _ ≤ 3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') := by
           exact mul_le_mul_left' (robust_projection_main.Nreal_mono_local (Set.image_mono hE3''_sub)) 3

  exact ⟨Gamma, hGamma_sub, hGamma_grid, hGamma_density, hGamma_third1', hGamma_third2, hGamma_witness⟩

end ProductLikeIncidence.ProductReduction
