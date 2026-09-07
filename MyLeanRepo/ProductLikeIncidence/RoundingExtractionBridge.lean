module

/-
# Rounding Extraction Bridge

Bridges production `ProjectedRoundingExtraction` and `DeltaSetTransfer`
to the skeleton's `rounding_layer` and `extract_A1_A2` signatures.

## Results

1. `rounding_layer_bridge` — round 1D measure to δ-grid with energy factor 3^(2κ0)
   and universal cell preimage transfer (factor 6).

2. `extract_A1_A2_bridge` — apply `projected_rounding_extraction_single` to both
   coordinate projections of a 2D measure. Returns grid sets S1, S2 (δ-separated,
   IsProductLikeRealDeltaSCSet) and a high-mass subset E3'' ⊆ E3' with
   μE3' E3'' ≥ 1/2 such that ∀ p ∈ E3'', round(p 0) ∈ S1 ∧ round(p 1) ∈ S2.
   No coordinate-wise separation assumed.

## Whiteprint node
`rounding_extraction_bridge`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.EnergyToLargeMassDeltaSet
public import MyLeanRepo.RoundingWrapper
public import MyLeanRepo.DeltaSetTransfer
public import MyLeanRepo.ProductLikeIncidence.ProjectedRoundingExtraction
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical Finset

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ### rounding_layer bridge -/

/-- Bridge for the skeleton's `rounding_layer`.

Given a probability measure μ on [0,1] with bounded Riesz energy, produce
a rounded measure μ_rounded on the δ-grid with:
- δ-separated support in [0,1]
- energy increases by at most 3^(2κ0)
- universal cell preimage transfer: any δ-grid δ-set S has preimage a δ-set with factor 6.

This uses `roundToDeltaGrid` directly (no need for the full S extraction
from `projected_rounding_extraction_single`). -/
lemma rounding_layer_bridge
    {δ κ0 η_total : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_lt_one : δ < 1)
    (hkappa_pos : 0 < κ0) (hη_total_pos : 0 < η_total)
    (hδ_kappa_small : δ ^ κ0 ≤ 1 / 128)
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h_supp : μ.support ⊆ Set.Icc 0 1)
    (h_energy : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ ≤
      ENNReal.ofReal (δ ^ (-η_total))) :
    ∃ (μ_rounded : Measure ℝ)
      (round_map : ℝ → ℝ),
      IsProbabilityMeasure μ_rounded ∧
      μ_rounded = Measure.map round_map μ ∧
      μ_rounded.support ⊆ productLikeIntegerGrid δ ∩ Set.Icc 0 1 ∧
      (∀ x ∈ μ_rounded.support, ∀ y ∈ μ_rounded.support, x ≠ y → |x - y| ≥ δ) ∧
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ_rounded ≤
        ENNReal.ofReal (3 ^ (2 * κ0) * δ ^ (-η_total)) ∧
      (∀ (S : Set ℝ) (C : ℝ),
        S ⊆ productLikeIntegerGrid δ →
        IsProductLikeRealDeltaSCSet δ κ0 C S →
        IsProductLikeRealDeltaSCSet δ κ0 (6 * C) (round_map ⁻¹' S)) := by
  let round_map : ℝ → ℝ := robust_projection_main.roundToDeltaGrid δ
  let μ_rounded : Measure ℝ := Measure.map round_map μ

  -- IsProbabilityMeasure
  have h_rounded_mass_one : μ_rounded Set.univ = 1 := by
    rw [Measure.map_apply (robust_projection_main.measurable_roundToDeltaGrid δ) MeasurableSet.univ]
    <;> simp [measure_univ]
  letI : IsProbabilityMeasure μ_rounded := ⟨h_rounded_mass_one⟩

  -- Gδ = rounded image of support
  let Gδ : Set ℝ := round_map '' μ.support

  have hGδ_grid : Gδ ⊆ productLikeIntegerGrid δ := by
    intro y hy
    rcases hy with ⟨x, _, rfl⟩
    have h1 : round_map x = δ * (round (x / δ) : ℝ) := by rfl
    rw [h1]; exact ⟨round (x / δ), by ring⟩

  rcases hδ_dyadic with ⟨n, hδ_eq⟩
  have h_rnd_Icc : ∀ x ∈ Set.Icc (0 : ℝ) 1, round_map x ∈ Set.Icc (0 : ℝ) 1 :=
    roundToDeltaGrid_maps_Icc hδ_pos n hδ_eq

  have hGδ_sub_Icc : Gδ ⊆ Set.Icc 0 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_rnd_Icc x (h_supp hx)

  have hGδ_bdd : Bornology.IsBounded Gδ :=
    Bornology.IsBounded.subset (Metric.isBounded_Icc 0 1) hGδ_sub_Icc

  have hGδ_finite : Set.Finite Gδ :=
    robust_projection_main.bounded_grid_subset_finite hδ_pos hGδ_grid hGδ_bdd

  have hGδ_supp : μ_rounded.support ⊆ Gδ := by
    have h_preimage_subset : round_map ⁻¹' (Gδᶜ) ⊆ (μ.support)ᶜ := by
      intro u hu
      have h3 : round_map u ∉ Gδ := hu
      by_contra h4
      have h4' : u ∈ μ.support := by simpa [Set.mem_compl_iff] using h4
      have h5 : round_map u ∈ Gδ := ⟨u, h4', rfl⟩
      exact h3 h5
    have h_null : μ (round_map ⁻¹' (Gδᶜ)) = 0 := by
      have h6 : μ (round_map ⁻¹' (Gδᶜ)) ≤ μ ((μ.support)ᶜ) := measure_mono h_preimage_subset
      have h7 : μ ((μ.support)ᶜ) = 0 := μ.measure_compl_support
      have h8 : μ (round_map ⁻¹' (Gδᶜ)) ≤ 0 := le_trans h6 (le_of_eq h7)
      exact le_zero_iff.mp h8
    have hGδ_closed : IsClosed Gδ := hGδ_finite.isClosed
    have hGδc_meas : MeasurableSet (Gδᶜ) := hGδ_closed.isOpen_compl.measurableSet
    have h_pushforward_null : μ_rounded Gδᶜ = 0 := by
      dsimp only [μ_rounded]
      rw [Measure.map_apply (robust_projection_main.measurable_roundToDeltaGrid δ) hGδc_meas]
      exact h_null
    have h_ae : Gδ ∈ MeasureTheory.ae μ_rounded := by
      simpa [MeasureTheory.mem_ae_iff] using h_pushforward_null
    exact MeasureTheory.Measure.support_subset_of_isClosed hGδ_closed h_ae

  have hGδ_sep : ∀ (x y : ℝ), x ∈ Gδ → y ∈ Gδ → x ≠ y → dist x y ≥ δ := by
    intro x y hx hy hxy
    have hxg : x ∈ productLikeIntegerGrid δ := hGδ_grid hx
    have hyg : y ∈ productLikeIntegerGrid δ := hGδ_grid hy
    rcases hxg with ⟨k, hkx⟩
    rcases hyg with ⟨m, hmy⟩
    have hkm : k ≠ m := by
      intro h
      have h1 : x = y := by
        calc x = δ * (k : ℝ) := hkx
          _ = δ * (m : ℝ) := by rw [h]
          _ = y := hmy.symm
      exact hxy h1
    have h9 : |(k : ℝ) - (m : ℝ)| ≥ 1 := by
      have h10 : (k : ℝ) ≠ (m : ℝ) := by exact_mod_cast hkm
      have h11 : |k - m| ≥ 1 := by apply Int.one_le_abs; omega
      have h12 : |(k : ℝ) - (m : ℝ)| = |(k - m : ℤ)| := by norm_cast
      rw [h12]; exact_mod_cast h11
    calc dist x y
      = dist (δ * (k : ℝ)) (δ * (m : ℝ)) := by rw [hkx, hmy]
    _ = |δ * (k : ℝ) - δ * (m : ℝ)| := by rw [Real.dist_eq]
    _ = |δ * ((k : ℝ) - (m : ℝ))| := by rw [mul_sub]
    _ = δ * |(k : ℝ) - (m : ℝ)| := by rw [abs_mul, abs_of_pos hδ_pos]
    _ ≥ δ * 1 := by gcongr
    _ = δ := by ring

  have h_supp_grid : μ_rounded.support ⊆ productLikeIntegerGrid δ :=
    subset_trans hGδ_supp hGδ_grid
  have h_supp_Icc : μ_rounded.support ⊆ Set.Icc 0 1 :=
    subset_trans hGδ_supp hGδ_sub_Icc
  have h_supp_inter : μ_rounded.support ⊆ productLikeIntegerGrid δ ∩ Set.Icc 0 1 := by
    intro x hx
    exact ⟨h_supp_grid hx, h_supp_Icc hx⟩

  have h_supp_sep : ∀ x ∈ μ_rounded.support, ∀ y ∈ μ_rounded.support, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hxy
    exact hGδ_sep x y (hGδ_supp hx) (hGδ_supp hy) hxy

  -- Energy bound
  have h_energy_round : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ_rounded ≤
      ENNReal.ofReal (3 ^ (2 * κ0) * δ ^ (-η_total)) := by
    have h1 := robust_projection_main.rounded_energy_bound hδ_pos hkappa_pos (ν := μ)
    calc robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ_rounded
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (2 * κ0)) * robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ := h1
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (2 * κ0)) * ENNReal.ofReal (δ ^ (-η_total)) := by
        gcongr <;> exact h_energy
    _ = ENNReal.ofReal (3 ^ (2 * κ0) * δ ^ (-η_total)) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl

  -- Universal cell preimage transfer
  have h_transfer : ∀ (S : Set ℝ) (C : ℝ),
      S ⊆ productLikeIntegerGrid δ →
      IsProductLikeRealDeltaSCSet δ κ0 C S →
      IsProductLikeRealDeltaSCSet δ κ0 (6 * C) (round_map ⁻¹' S) := by
    intro S C hS_grid hS_delta
    exact robust_projection_main.local_delta_set_transfer hδ_pos hS_grid hS_delta

  exact ⟨μ_rounded, round_map, inferInstance, rfl, h_supp_inter, h_supp_sep, h_energy_round, h_transfer⟩

/-! ### extract_A1_A2 bridge (V2: no coordinate separation) -/

/-- Extract coordinate δ-sets S1, S2 and a high-mass subset E3'' from a 2D measure.

Applies `projected_rounding_extraction_single` to each coordinate projection
separately. No coordinate-wise separation is assumed.

Define E3'' = E3' ∩ proj_x⁻¹(A_source1) ∩ proj_y⁻¹(A_source2).
By union bound, μE3' E3'' ≥ 1 - 1/4 - 1/4 = 1/2.
For p ∈ E3'', round(p 0) ∈ S1 and round(p 1) ∈ S2. -/
lemma extract_A1_A2_bridge
    {δ κ0 η_total η_energy C_energy C_extract : ℝ}
    (hδ_pos : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales) (hδ_lt_one : δ < 1)
    (hkappa_pos : 0 < κ0) (hκ0_le_one : κ0 ≤ 1)
    (hη_total_pos : 0 < η_total) (hη_energy_pos : 0 < η_energy)
    (hδ_kappa_small : δ ^ κ0 ≤ 1 / 128)
    (hC_extract_pos : 0 < C_extract)
    -- Energy absorption: C_energy * δ^(-η_total) ≤ δ^(-η_energy)
    (h_energy_absorb : C_energy * δ ^ (-η_total) ≤ δ ^ (-η_energy))
    -- Extract constant bound
    (hC_extract_large : robust_projection_main.energyToLargeMassDeltaSetC δ κ0
        ((3 : ℝ) ^ (2 * κ0) * δ ^ (-η_energy)) ≤ C_extract)
    {μE3' : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE3']
    {E3' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3'_supp : μE3'.support = E3')
    (hE3'_unit : ∀ p ∈ E3', p 0 ∈ Set.Icc 0 1 ∧ p 1 ∈ Set.Icc 0 1)
    -- Energy bounds for coordinate projections (from Kaufman + FourSectorChart)
    (h_energy_x : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p => p 0) μE3') ≤
      ENNReal.ofReal (C_energy * δ ^ (-η_total)))
    (h_energy_y : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos
        (Measure.map (fun p => p 1) μE3') ≤
      ENNReal.ofReal (C_energy * δ ^ (-η_total))) :
    ∃ (round : ℝ → ℝ) (S1 S2 : Set ℝ) (E3'' : Set (EuclideanSpace ℝ (Fin 2))),
      round = robust_projection_main.roundToDeltaGrid δ ∧
      (∀ x, |x - round x| ≤ δ / 2) ∧
      S1 ⊆ productLikeIntegerGrid δ ∧
      S2 ⊆ productLikeIntegerGrid δ ∧
      (∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ) ∧
      (∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ) ∧
      S1 ⊆ (robust_projection_main.roundToDeltaGrid δ) '' (Set.image (fun p => p 0) E3') ∧
      S2 ⊆ (robust_projection_main.roundToDeltaGrid δ) '' (Set.image (fun p => p 1) E3') ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S1 ∧
      IsProductLikeRealDeltaSCSet δ κ0 C_extract S2 ∧
      E3'' ⊆ E3' ∧
      μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ) ∧
      (∀ p ∈ E3'', round (p 0) ∈ S1 ∧ round (p 1) ∈ S2) := by
  let proj_x : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 0
  let proj_y : EuclideanSpace ℝ (Fin 2) → ℝ := fun p => p 1
  let μ_x : Measure ℝ := Measure.map proj_x μE3'
  let μ_y : Measure ℝ := Measure.map proj_y μE3'

  -- μ_x is probability
  have hμx_univ : μ_x Set.univ = 1 := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] <;> simp
  letI : IsProbabilityMeasure μ_x := ⟨hμx_univ⟩

  -- μ_y is probability
  have hμy_univ : μ_y Set.univ = 1 := by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] <;> simp
  letI : IsProbabilityMeasure μ_y := ⟨hμy_univ⟩

  -- Support of μ_x in [0,1]
  have hμx_supp : μ_x.support ⊆ Set.Icc 0 1 := by
    have h_null : μ_x ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
      have h1 : μ_x ((Set.Icc (0 : ℝ) 1)ᶜ) = μE3' (proj_x ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) := by
        rw [Measure.map_apply (by fun_prop) isClosed_Icc.isOpen_compl.measurableSet]
      rw [h1]
      have h2 : proj_x ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ ⊆ (μE3'.support)ᶜ := by
        intro p hp h3
        have h4 : p ∈ E3' := by rwa [hE3'_supp] at h3
        have h5 : proj_x p ∈ Set.Icc (0 : ℝ) 1 := (hE3'_unit p h4).1
        exact hp h5
      exact measure_mono_null h2 μE3'.measure_compl_support
    have h_ae : (Set.Icc (0 : ℝ) 1) ∈ MeasureTheory.ae μ_x := by
      simpa [MeasureTheory.mem_ae_iff] using h_null
    exact MeasureTheory.Measure.support_subset_of_isClosed isClosed_Icc h_ae

  -- Support of μ_y in [0,1]
  have hμy_supp : μ_y.support ⊆ Set.Icc 0 1 := by
    have h_null : μ_y ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 := by
      have h1 : μ_y ((Set.Icc (0 : ℝ) 1)ᶜ) = μE3' (proj_y ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ) := by
        rw [Measure.map_apply (by fun_prop) isClosed_Icc.isOpen_compl.measurableSet]
      rw [h1]
      have h2 : proj_y ⁻¹' (Set.Icc (0 : ℝ) 1)ᶜ ⊆ (μE3'.support)ᶜ := by
        intro p hp h3
        have h4 : p ∈ E3' := by rwa [hE3'_supp] at h3
        have h5 : proj_y p ∈ Set.Icc (0 : ℝ) 1 := (hE3'_unit p h4).2
        exact hp h5
      exact measure_mono_null h2 μE3'.measure_compl_support
    have h_ae : (Set.Icc (0 : ℝ) 1) ∈ MeasureTheory.ae μ_y := by
      simpa [MeasureTheory.mem_ae_iff] using h_null
    exact MeasureTheory.Measure.support_subset_of_isClosed isClosed_Icc h_ae

  -- Adapt energy bounds
  have h_energy_x' : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ_x ≤
      ENNReal.ofReal (δ ^ (-η_energy)) := by
    calc
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ_x
        ≤ ENNReal.ofReal (C_energy * δ ^ (-η_total)) := h_energy_x
      _ ≤ ENNReal.ofReal (δ ^ (-η_energy)) := by
        exact ENNReal.ofReal_le_ofReal h_energy_absorb

  have h_energy_y' : robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ_y ≤
      ENNReal.ofReal (δ ^ (-η_energy)) := by
    calc
      robust_projection_main.rieszEnergy (2 * κ0) hδ_pos μ_y
        ≤ ENNReal.ofReal (C_energy * δ ^ (-η_total)) := h_energy_y
      _ ≤ ENNReal.ofReal (δ ^ (-η_energy)) := by
        exact ENNReal.ofReal_le_ofReal h_energy_absorb

  -- Apply production theorem to x-projection
  -- Use shallow destructuring to avoid dependent-elimination issues with Nreal μ.support
  have h_x := projected_rounding_extraction_single
      hδ_pos hδ_lt_one hδ_dyadic hkappa_pos hκ0_le_one hη_energy_pos hC_extract_pos
      hδ_kappa_small hμx_supp h_energy_x' hC_extract_large
  rcases h_x with ⟨round1, S1_finset, A_cells1, A_source1, rounded_mu1,
    h_rmu1_eq, h_round1_eq, hS1_grid, hS1_sep, h_rmu1_mass,
    hA_cells1_eq, hA_source1_eq, h_mass1, hA_source1_sub,
    hS1_delta, hA_cells1_delta, h_rest_x⟩
  have hNreal1_1 : Nreal δ A_source1 ≤ 2 * Nreal δ (S1_finset : Set ℝ) := by
    exact And.left h_rest_x
  have hNreal1_2 : Nreal δ A_source1 ≤ Nreal δ μ_x.support := by
    exact And.left (And.right h_rest_x)
  have hS1_sub_Gδ : (S1_finset : Set ℝ) ⊆ round1 '' μ_x.support := by
    exact And.right (And.right h_rest_x)

  -- Apply production theorem to y-projection
  have h_y := projected_rounding_extraction_single
      hδ_pos hδ_lt_one hδ_dyadic hkappa_pos hκ0_le_one hη_energy_pos hC_extract_pos
      hδ_kappa_small hμy_supp h_energy_y' hC_extract_large
  rcases h_y with ⟨round2, S2_finset, A_cells2, A_source2, rounded_mu2,
    h_rmu2_eq, h_round2_eq, hS2_grid, hS2_sep, h_rmu2_mass,
    hA_cells2_eq, hA_source2_eq, h_mass2, hA_source2_sub,
    hS2_delta, hA_cells2_delta, h_rest_y⟩
  have hNreal2_1 : Nreal δ A_source2 ≤ 2 * Nreal δ (S2_finset : Set ℝ) := by
    exact And.left h_rest_y
  have hNreal2_2 : Nreal δ A_source2 ≤ Nreal δ μ_y.support := by
    exact And.left (And.right h_rest_y)
  have hS2_sub_Gδ : (S2_finset : Set ℝ) ⊆ round2 '' μ_y.support := by
    exact And.right (And.right h_rest_y)

  let round : ℝ → ℝ := robust_projection_main.roundToDeltaGrid δ
  let S1 : Set ℝ := (S1_finset : Set ℝ)
  let S2 : Set ℝ := (S2_finset : Set ℝ)

  have h_round_eq : round = robust_projection_main.roundToDeltaGrid δ := rfl
  have h_round1_eq' : round1 = round := by simpa [round] using h_round1_eq
  have h_round2_eq' : round2 = round := by simpa [round] using h_round2_eq

  -- Rounding proximity
  have h_round_near : ∀ x, |x - round x| ≤ δ / 2 :=
    robust_projection_main.abs_sub_roundToDeltaGrid hδ_pos

  -- S1 properties
  have hS1_grid' : S1 ⊆ productLikeIntegerGrid δ := by
    intro x hx
    exact hS1_grid x hx
  have hS1_sep' : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hxy
    exact hS1_sep x hx y hy hxy
  have hS1_delta' : IsProductLikeRealDeltaSCSet δ κ0 C_extract S1 := hS1_delta

  -- S2 properties
  have hS2_grid' : S2 ⊆ productLikeIntegerGrid δ := by
    intro x hx
    exact hS2_grid x hx
  have hS2_sep' : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ := by
    intro x hx y hy hxy
    exact hS2_sep x hx y hy hxy
  have hS2_delta' : IsProductLikeRealDeltaSCSet δ κ0 C_extract S2 := hS2_delta

  -- A_source1 = μ_x.support ∩ round ⁻¹' S1
  have hA_source1_eq' : A_source1 = μ_x.support ∩ round ⁻¹' S1 := by
    rw [hA_source1_eq, hA_cells1_eq, h_round1_eq'] <;> rfl
  have hA_source1_meas : MeasurableSet A_source1 := by
    rw [hA_source1_eq']
    have h1 : MeasurableSet μ_x.support := MeasureTheory.Measure.isClosed_support.measurableSet
    have h2 : MeasurableSet (round ⁻¹' S1) := (Finset.finite_toSet S1_finset).measurableSet.preimage (robust_projection_main.measurable_roundToDeltaGrid δ)
    exact h1.inter h2

  -- A_source2 = μ_y.support ∩ round ⁻¹' S2
  have hA_source2_eq' : A_source2 = μ_y.support ∩ round ⁻¹' S2 := by
    rw [hA_source2_eq, hA_cells2_eq, h_round2_eq']
  have hA_source2_meas : MeasurableSet A_source2 := by
    rw [hA_source2_eq']
    have h1 : MeasurableSet μ_y.support := MeasureTheory.Measure.isClosed_support.measurableSet
    have h2 : MeasurableSet (round ⁻¹' S2) := (Finset.finite_toSet S2_finset).measurableSet.preimage (robust_projection_main.measurable_roundToDeltaGrid δ)
    exact h1.inter h2

  -- Define B1, B2 as preimages in E3'
  let B1 : Set (EuclideanSpace ℝ (Fin 2)) := proj_x ⁻¹' A_source1
  let B2 : Set (EuclideanSpace ℝ (Fin 2)) := proj_y ⁻¹' A_source2

  have hB1_meas : MeasurableSet B1 := hA_source1_meas.preimage (by fun_prop)
  have hB2_meas : MeasurableSet B2 := hA_source2_meas.preimage (by fun_prop)

  -- μE3' B1 = μ_x A_source1 ≥ 3/4
  have hμB1 : μE3' B1 = μ_x A_source1 := by
    dsimp only [B1, μ_x]
    rw [Measure.map_apply (by fun_prop) hA_source1_meas]
  have hμB1_ge : μE3' B1 ≥ ENNReal.ofReal (3 / 4 : ℝ) := by
    rw [hμB1]
    exact h_mass1

  -- μE3' B2 = μ_y A_source2 ≥ 3/4
  have hμB2 : μE3' B2 = μ_y A_source2 := by
    dsimp only [B2, μ_y]
    rw [Measure.map_apply (by fun_prop) hA_source2_meas]
  have hμB2_ge : μE3' B2 ≥ ENNReal.ofReal (3 / 4 : ℝ) := by
    rw [hμB2]
    exact h_mass2

  -- Define E3'' = E3' ∩ B1 ∩ B2
  let E3'' : Set (EuclideanSpace ℝ (Fin 2)) := E3' ∩ B1 ∩ B2

  have hE3''_sub : E3'' ⊆ E3' := by
    intro p hp
    exact hp.1.1

  -- For p ∈ E3'', round(p 0) ∈ S1 and round(p 1) ∈ S2
  have hE3''_round : ∀ p ∈ E3'', round (p 0) ∈ S1 ∧ round (p 1) ∈ S2 := by
    intro p hp
    have h_p_in_B1 : p ∈ B1 := hp.1.2
    have h_p_in_B2 : p ∈ B2 := hp.2
    have h1 : p 0 ∈ A_source1 := h_p_in_B1
    have h2 : p 1 ∈ A_source2 := h_p_in_B2
    have h3 : p 0 ∈ round ⁻¹' S1 := by
      rw [hA_source1_eq'] at h1
      exact h1.2
    have h4 : p 1 ∈ round ⁻¹' S2 := by
      rw [hA_source2_eq'] at h2
      exact h2.2
    exact ⟨h3, h4⟩

  -- Mass bound: μE3' E3'' ≥ 1/2 by union bound
  have hE3'_full : μE3' E3' = 1 := by
    rw [← hE3'_supp]
    have h1 : μE3' (μE3'.supportᶜ) = 0 := μE3'.measure_compl_support
    have h_support_closed : IsClosed μE3'.support := by exact Measure.isClosed_support
    have h_compl_meas : MeasurableSet (μE3'.supportᶜ) := h_support_closed.isOpen_compl.measurableSet
    have h2 : μE3' (μE3'.support ∪ μE3'.supportᶜ) + μE3' (μE3'.support ∩ μE3'.supportᶜ) =
        μE3' μE3'.support + μE3' (μE3'.supportᶜ) :=
      MeasureTheory.measure_union_add_inter μE3'.support h_compl_meas
    have h3 : μE3' Set.univ = μE3' μE3'.support + μE3' (μE3'.supportᶜ) := by
      simpa [Set.union_compl_self] using h2
    have h4 : μE3' Set.univ = 1 := measure_univ
    rw [h4] at h3
    rw [h1] at h3
    have h5 : (1 : ENNReal) = μE3' μE3'.support + 0 := h3
    simpa using h5.symm

  have hB1_inter_B2_meas : MeasurableSet (B1 ∩ B2) := hB1_meas.inter hB2_meas

  -- All measures are ≤ 1 since μE3' is probability
  have h_le_one : ∀ (s : Set (EuclideanSpace ℝ (Fin 2))), μE3' s ≤ 1 := by
    intro s
    have h : μE3' s ≤ μE3' Set.univ := measure_mono (Set.subset_univ s)
    rw [measure_univ] at h
    exact h
  have h_ne_top : ∀ (s : Set (EuclideanSpace ℝ (Fin 2))), μE3' s ≠ ⊤ := by
    intro s
    have h : μE3' s ≤ 1 := h_le_one s
    exact ne_top_of_le_ne_top (by simp) h

  -- Inclusion-exclusion
  have h_union_eq : μE3' (B1 ∪ B2) + μE3' (B1 ∩ B2) = μE3' B1 + μE3' B2 :=
    MeasureTheory.measure_union_add_inter B1 hB2_meas

  -- Convert to real for arithmetic
  have h_real_eq : (μE3' (B1 ∪ B2)).toReal + (μE3' (B1 ∩ B2)).toReal =
      (μE3' B1).toReal + (μE3' B2).toReal := by
    have h_add : (μE3' (B1 ∪ B2) + μE3' (B1 ∩ B2)).toReal =
        (μE3' (B1 ∪ B2)).toReal + (μE3' (B1 ∩ B2)).toReal := by
      rw [ENNReal.toReal_add (h_ne_top _) (h_ne_top _)]
    have h_add2 : (μE3' B1 + μE3' B2).toReal =
        (μE3' B1).toReal + (μE3' B2).toReal := by
      rw [ENNReal.toReal_add (h_ne_top _) (h_ne_top _)]
    rw [← h_add, ← h_add2, h_union_eq]

  have h_real1 : (μE3' B1).toReal ≥ 3 / 4 := by
    have h : ENNReal.ofReal (3 / 4 : ℝ) ≤ μE3' B1 := hμB1_ge
    have h' : (ENNReal.ofReal (3 / 4 : ℝ)).toReal ≤ (μE3' B1).toReal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (h_ne_top _)).mpr h
    have h_ofReal : (ENNReal.ofReal (3 / 4 : ℝ)).toReal = (3 / 4 : ℝ) := ENNReal.toReal_ofReal (by norm_num)
    rw [h_ofReal] at h'
    exact h'
  have h_real2 : (μE3' B2).toReal ≥ 3 / 4 := by
    have h : ENNReal.ofReal (3 / 4 : ℝ) ≤ μE3' B2 := hμB2_ge
    have h' : (ENNReal.ofReal (3 / 4 : ℝ)).toReal ≤ (μE3' B2).toReal :=
      (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (h_ne_top _)).mpr h
    have h_ofReal : (ENNReal.ofReal (3 / 4 : ℝ)).toReal = (3 / 4 : ℝ) := ENNReal.toReal_ofReal (by norm_num)
    rw [h_ofReal] at h'
    exact h'
  have h_real_u : (μE3' (B1 ∪ B2)).toReal ≤ 1 := by
    have h : μE3' (B1 ∪ B2) ≤ (1 : ENNReal) := h_le_one _
    have h' : (μE3' (B1 ∪ B2)).toReal ≤ (1 : ENNReal).toReal :=
      (ENNReal.toReal_le_toReal (h_ne_top _) (by exact one_ne_top)).mpr h
    have h_one : (1 : ENNReal).toReal = (1 : ℝ) := by simp
    rw [h_one] at h'
    exact h'
  have h_real_i : (μE3' (B1 ∩ B2)).toReal ≥ 1 / 2 := by linarith
  have h_main_mass : μE3' (B1 ∩ B2) ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
    have h' : (ENNReal.ofReal (1 / 2 : ℝ)).toReal ≤ (μE3' (B1 ∩ B2)).toReal := by
      simpa using h_real_i
    exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (h_ne_top _)).mp h'

  -- E3'' = E3' ∩ (B1 ∩ B2), and E3' has full measure
  have hE3''_eq : μE3' E3'' = μE3' (B1 ∩ B2) := by
    have h9 : E3'' = E3' ∩ (B1 ∩ B2) := by
      ext p
      simp [E3''] <;> tauto
    rw [h9]
    have h10 : μE3' (E3' ∩ (B1 ∩ B2)) = μE3' (B1 ∩ B2) := by
      have h11 : (B1 ∩ B2) \ E3' ⊆ (μE3'.support)ᶜ := by
        intro p hp
        have h12 : p ∉ E3' := hp.2
        rw [hE3'_supp]
        exact h12
      have h13 : μE3' ((B1 ∩ B2) \ E3') = 0 :=
        measure_mono_null h11 μE3'.measure_compl_support
      have hE3'_meas : MeasurableSet E3' := by
        rw [← hE3'_supp]
        exact MeasureTheory.Measure.isClosed_support.measurableSet
      have h14 : μE3' (B1 ∩ B2) = μE3' (E3' ∩ (B1 ∩ B2)) + μE3' ((B1 ∩ B2) \ E3') := by
        rw [← MeasureTheory.measure_inter_add_sdiff (B1 ∩ B2) hE3'_meas]
        <;> simp [Set.inter_comm]
      rw [h13] at h14
      simpa using h14.symm
    exact h10

  have hE3''_mass : μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [hE3''_eq]
    exact h_main_mass

  -- S1 ⊆ round '' (image proj_x E3')
  have hE3'_bounded : Bornology.IsBounded E3' := by
    have h1 : E3' ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt 2) := by
      intro p hp
      have h2 : p 0 ∈ Set.Icc (0 : ℝ) 1 := (hE3'_unit p hp).1
      have h3 : p 1 ∈ Set.Icc (0 : ℝ) 1 := (hE3'_unit p hp).2
      have h4 : ‖p‖ ≤ Real.sqrt 2 := by
        rw [EuclideanSpace.norm_eq]
        have h2' : ‖p 0‖ = p 0 := by
          rw [Real.norm_eq_abs, abs_of_nonneg h2.1]
        have h3' : ‖p 1‖ = p 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg h3.1]
        have h5 : ∑ i : Fin 2, ‖p i‖ ^ 2 ≤ 2 := by
          rw [Fin.sum_univ_two, h2', h3']
          nlinarith [h2.1, h2.2, h3.1, h3.2]
        exact Real.sqrt_le_sqrt h5
      simpa [Metric.mem_closedBall, dist_zero_right] using h4
    have h_bdd_ball : Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt 2)) := by exact Metric.isBounded_closedBall
    exact h_bdd_ball.subset h1
  have hE3'_closed : IsClosed E3' := by
    rw [← hE3'_supp]; exact MeasureTheory.Measure.isClosed_support
  have hE3'_compact : IsCompact E3' := by
    have h : IsCompact E3' := by
      exact Metric.isCompact_of_isClosed_isBounded hE3'_closed hE3'_bounded
    exact h
  have h_image_x_closed : IsClosed (Set.image proj_x E3') :=
    (hE3'_compact.image (by fun_prop)).isClosed
  have hμx_supp_sub : μ_x.support ⊆ Set.image proj_x E3' := by
    intro x hx
    by_contra h_notin
    let U := (Set.image proj_x E3')ᶜ
    have hU_open : IsOpen U := h_image_x_closed.isOpen_compl
    have hxU : x ∈ U := h_notin
    have h_preimage_sub : proj_x ⁻¹' U ⊆ (μE3'.support)ᶜ := by
      intro p hp
      have h1 : proj_x p ∈ U := hp
      simp only [U, Set.mem_compl_iff] at h1 ⊢
      intro h2
      have h2' : p ∈ E3' := by rw [←hE3'_supp]; exact h2
      exact h1 ⟨p, h2', rfl⟩
    have h_null : μE3' (proj_x ⁻¹' U) = 0 :=
      measure_mono_null h_preimage_sub μE3'.measure_compl_support
    have hμxU : μ_x U = 0 := by
      dsimp only [μ_x]
      rw [Measure.map_apply (by fun_prop) hU_open.measurableSet]
      exact h_null
    have h_contra : x ∉ μ_x.support := by
      intro hx_supp
      have h_supp_iff : x ∈ μ_x.support ↔ ∀ (V : Set ℝ), V ∈ nhds x → 0 < μ_x V :=
        MeasureTheory.Measure.mem_support_iff_forall x
      have h' : ∀ (V : Set ℝ), V ∈ nhds x → 0 < μ_x V := h_supp_iff.mp hx_supp
      have hU_nhds : U ∈ nhds x := hU_open.mem_nhds hxU
      have h_pos : 0 < μ_x U := h' U hU_nhds
      rw [hμxU] at h_pos
      exact False.elim (lt_irrefl 0 h_pos)
    exact h_contra hx
  have hS1_sub_round : S1 ⊆ (robust_projection_main.roundToDeltaGrid δ) '' (Set.image proj_x E3') := by
    have h1 : S1 ⊆ round1 '' μ_x.support := hS1_sub_Gδ
    have h2 : round1 '' μ_x.support ⊆ round1 '' (Set.image proj_x E3') :=
      Set.image_mono hμx_supp_sub
    have h3 : S1 ⊆ round1 '' (Set.image proj_x E3') := subset_trans h1 h2
    have h4 : round1 = robust_projection_main.roundToDeltaGrid δ := h_round1_eq'
    rw [h4] at h3
    exact h3
  have hμy_supp_sub : μ_y.support ⊆ Set.image proj_y E3' := by
    intro x hx
    by_contra h_notin
    let U := (Set.image proj_y E3')ᶜ
    have hU_open : IsOpen U := (hE3'_compact.image (by fun_prop)).isClosed.isOpen_compl
    have hxU : x ∈ U := h_notin
    have h_preimage_sub : proj_y ⁻¹' U ⊆ (μE3'.support)ᶜ := by
      intro p hp
      have h1 : proj_y p ∈ U := hp
      simp only [U, Set.mem_compl_iff] at h1 ⊢
      intro h2
      have h2' : p ∈ E3' := by rw [←hE3'_supp]; exact h2
      exact h1 ⟨p, h2', rfl⟩
    have h_null : μE3' (proj_y ⁻¹' U) = 0 :=
      measure_mono_null h_preimage_sub μE3'.measure_compl_support
    have hμyU : μ_y U = 0 := by
      dsimp only [μ_y]
      rw [Measure.map_apply (by fun_prop) hU_open.measurableSet]
      exact h_null
    have h_contra : x ∉ μ_y.support := by
      intro hx_supp
      have h_supp_iff : x ∈ μ_y.support ↔ ∀ (V : Set ℝ), V ∈ nhds x → 0 < μ_y V :=
        MeasureTheory.Measure.mem_support_iff_forall x
      have h' : ∀ (V : Set ℝ), V ∈ nhds x → 0 < μ_y V := h_supp_iff.mp hx_supp
      have hU_nhds : U ∈ nhds x := hU_open.mem_nhds hxU
      have h_pos : 0 < μ_y U := h' U hU_nhds
      rw [hμyU] at h_pos
      exact False.elim (lt_irrefl 0 h_pos)
    exact h_contra hx
  have hS2_sub_round : S2 ⊆ (robust_projection_main.roundToDeltaGrid δ) '' (Set.image proj_y E3') := by
    have h1 : S2 ⊆ round2 '' μ_y.support := hS2_sub_Gδ
    have h2 : round2 '' μ_y.support ⊆ round2 '' (Set.image proj_y E3') :=
      Set.image_mono hμy_supp_sub
    have h3 : S2 ⊆ round2 '' (Set.image proj_y E3') := subset_trans h1 h2
    have h4 : round2 = robust_projection_main.roundToDeltaGrid δ := h_round2_eq'
    rw [h4] at h3
    exact h3

  exact ⟨round, S1, S2, E3'', h_round_eq, h_round_near,
    hS1_grid', hS2_grid', hS1_sep', hS2_sep',
    hS1_sub_round, hS2_sub_round,
    hS1_delta', hS2_delta',
    hE3''_sub, hE3''_mass, hE3''_round⟩

end ProductLikeIncidence.ProductReduction
