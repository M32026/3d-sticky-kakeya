module

/-
# Projected Rounding Extraction (Obligation 3 — corrected)

Given a probability measure μ on ℝ supported in [0,1] with bounded Riesz energy,
round to the δ-grid using production `RoundingWrapper`, extract a δ-set S,
and return S, A_cells = round⁻¹(S), and A_source = support(μ) ∩ A_cells.

A_cells inherits IsRealDeltaSet regularity via the factor-6 transfer theorem.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.Energy.EnergyToLargeMassDeltaSet
public import MyLeanRepo.RoundingWrapper
public import MyLeanRepo.DeltaSetTransfer
public import MyLeanRepo.ProductLikeIncidence.CoefficientRounding
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Bornology Classical Finset

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Monotonicity of `IsRealDeltaSet` in the constant `C`. -/
lemma isRealDeltaSet_mono_C {δ s C1 C2 : ℝ} {A : Set ℝ}
    (h : IsRealDeltaSet δ s C1 A) (hC : C1 ≤ C2) :
    IsRealDeltaSet δ s C2 A := by
  simp only [IsRealDeltaSet, IsDeltaSCSet] at h ⊢
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨h1, h2, h3, h4, h5, h6, h7, hC2_pos, ?_⟩
  intro r Q hr hQ hδr hr1
  have h10 := h9 hr hQ hδr hr1
  have h11 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := by exact ofReal_le_ofReal hC
  calc ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A ∩ Q))
    ≤ ENNReal.ofReal C1 * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) * ENNReal.ofReal (r ^ s) := h10
  _ ≤ ENNReal.ofReal C2 * ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) * ENNReal.ofReal (r ^ s) := by
    gcongr

/-- Rounding maps `[0,1]` into `[0,1]` for dyadic `δ = 2^{-n}`. -/
lemma roundToDeltaGrid_maps_Icc {δ : ℝ} (hδ_pos : 0 < δ) (n : ℕ)
    (hδ_eq : δ = (2 : ℝ)^(-(n : ℤ))) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, robust_projection_main.roundToDeltaGrid δ x ∈ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  have hx1 : 0 ≤ x := hx.1
  have hx2 : x ≤ 1 := hx.2
  have h1 : 0 ≤ x / δ := by positivity
  have h2 : x / δ ≤ ((2 ^ n : ℕ) : ℝ) := by
    have h3 : 1 / δ = ((2 ^ n : ℕ) : ℝ) := by
      simp [hδ_eq, zpow_neg] <;> field_simp <;> norm_cast
    have h4 : x / δ ≤ 1 / δ := by gcongr
    rw [h3] at h4; exact h4
  let k : ℤ := round (x / δ)
  have hk_nonneg : 0 ≤ k := by
    have h_eq : k = Int.floor (x / δ + 1 / 2) := by simp [k, round_eq]
    rw [h_eq]
    have h_pos : 0 ≤ x / δ + 1 / 2 := by linarith
    exact (Int.floor_nonneg).mpr h_pos
  have hk_le : k ≤ (2 ^ n : ℤ) := by
    have h1 : (k : ℝ) ≤ x / δ + 1 / 2 := round_le_add_half (x / δ)
    have h2 : (k : ℝ) < ((2 ^ n : ℕ) : ℝ) + 1 := by linarith
    by_contra h3
    have h4 : k > (2 ^ n : ℤ) := by exact lt_of_not_ge h3
    have h5 : k ≥ (2 ^ n : ℤ) + 1 := by linarith
    have h6 : (k : ℝ) ≥ (((2 ^ n : ℤ) + 1) : ℝ) := by exact_mod_cast h5
    have h7 : (((2 ^ n : ℤ) + 1) : ℝ) = ((2 ^ n : ℕ) : ℝ) + 1 := by
      simp [Nat.cast_add] <;> norm_cast <;> ring
    rw [h7] at h6
    linarith
  have h_result1 : 0 ≤ δ * (k : ℝ) := by positivity
  have h_result2 : δ * (k : ℝ) ≤ 1 := by
    have h5 : (k : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hk_le
    have h6 : δ * (k : ℝ) ≤ δ * ((2 ^ n : ℕ) : ℝ) := by gcongr
    have h7 : δ * ((2 ^ n : ℕ) : ℝ) = 1 := by
      simp [hδ_eq, zpow_neg] <;> field_simp <;> norm_cast
    rw [h7] at h6; exact h6
  exact ⟨h_result1, h_result2⟩

/-- **Projected rounding extraction** (core, support in `[0,1]`).

Returns S (δ-separated grid set with IsRealDeltaSet), A_cells = round⁻¹(S)
(with inherited IsRealDeltaSet at factor 6), and A_source = support(μ) ∩ A_cells
(with mass ≥ 3/4 and covering bounds). -/
lemma projected_rounding_extraction_single
    {δ κ η_energy C_extract : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hδ_dyadic : δ ∈ dyadicScales)
    (hκ_pos : 0 < κ) (hκ_le_one : κ ≤ 1)
    (hη_energy_pos : 0 < η_energy) (hC_extract_pos : 0 < C_extract)
    (hδ_small : δ ^ κ ≤ 1 / 128)
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h_supp_in_Icc : μ.support ⊆ Set.Icc 0 1)
    (h_energy : robust_projection_main.rieszEnergy (2 * κ) hδ_pos μ ≤
      ENNReal.ofReal (δ ^ (-η_energy)))
    (hC_extract_large : robust_projection_main.energyToLargeMassDeltaSetC δ κ
        ((3 : ℝ) ^ (2 * κ) * δ ^ (-η_energy)) ≤ C_extract) :
    ∃ (round : ℝ → ℝ)
      (S : Finset ℝ)
      (A_cells A_source : Set ℝ)
      (rounded_mu : Measure ℝ),
      rounded_mu = robust_projection_main.pushforwardRound δ μ ∧
      round = robust_projection_main.roundToDeltaGrid δ ∧
      (∀ x ∈ S, ∃ k : ℤ, x = δ * (k : ℝ)) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≥ δ) ∧
      rounded_mu (S : Set ℝ) ≥ ENNReal.ofReal (3 / 4 : ℝ) ∧
      A_cells = round ⁻¹' (S : Set ℝ) ∧
      A_source = μ.support ∩ A_cells ∧
      μ A_source ≥ ENNReal.ofReal (3 / 4 : ℝ) ∧
      A_source ⊆ μ.support ∧
      IsRealDeltaSet δ κ C_extract (S : Set ℝ) ∧
      IsRealDeltaSet δ κ (6 * C_extract) A_cells ∧
      Nreal δ A_source ≤ 2 * Nreal δ (S : Set ℝ) ∧
      Nreal δ A_source ≤ Nreal δ μ.support ∧
      (S : Set ℝ) ⊆ round '' μ.support := by
  have hδ_dyadic' := hδ_dyadic
  rcases hδ_dyadic with ⟨n, hδ_eq⟩

  let rnd := robust_projection_main.roundToDeltaGrid δ
  let rounded_mu := robust_projection_main.pushforwardRound δ μ

  have h_rnd_Icc : ∀ x ∈ Set.Icc (0 : ℝ) 1, rnd x ∈ Set.Icc (0 : ℝ) 1 :=
    roundToDeltaGrid_maps_Icc hδ_pos n hδ_eq

  have h_support_bdd : Bornology.IsBounded μ.support :=
    Bornology.IsBounded.subset (Metric.isBounded_Icc 0 1) h_supp_in_Icc

  -- Define Gδ explicitly as the rounded image of μ.support
  let Gδ : Set ℝ := rnd '' μ.support

  have hGδ_grid : Gδ ⊆ productLikeIntegerGrid δ := by
    intro y hy
    rcases hy with ⟨x, _, rfl⟩
    have h1 : rnd x = δ * (round (x / δ) : ℝ) := by
      dsimp only [rnd, robust_projection_main.roundToDeltaGrid] <;> rfl
    rw [h1]
    exact ⟨round (x / δ), by ring⟩

  have hGδ_sub_Icc : Gδ ⊆ Set.Icc 0 1 := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact h_rnd_Icc x (h_supp_in_Icc hx)

  have hGδ_bdd : Bornology.IsBounded Gδ :=
    Bornology.IsBounded.subset (Metric.isBounded_Icc 0 1) hGδ_sub_Icc

  have hGδ_finite : Set.Finite Gδ :=
    robust_projection_main.bounded_grid_subset_finite hδ_pos hGδ_grid hGδ_bdd

  have hGδ_supp : rounded_mu.support ⊆ Gδ := by
    have h_preimage_subset : rnd ⁻¹' (Gδᶜ) ⊆ (μ.support)ᶜ := by
      intro u hu
      have h3 : rnd u ∉ Gδ := hu
      by_contra h4
      have h4' : u ∈ μ.support := by simpa [Set.mem_compl_iff] using h4
      have h5 : rnd u ∈ Gδ := ⟨u, h4', rfl⟩
      exact h3 h5
    have h_null : μ (rnd ⁻¹' (Gδᶜ)) = 0 := by
      have h6 : μ (rnd ⁻¹' (Gδᶜ)) ≤ μ ((μ.support)ᶜ) := measure_mono h_preimage_subset
      have h7 : μ ((μ.support)ᶜ) = 0 := μ.measure_compl_support
      have h8 : μ (rnd ⁻¹' (Gδᶜ)) ≤ 0 := le_trans h6 (le_of_eq h7)
      exact le_zero_iff.mp h8
    have hGδ_closed : IsClosed Gδ := hGδ_finite.isClosed
    have hGδc_meas : MeasurableSet (Gδᶜ) := hGδ_closed.isOpen_compl.measurableSet
    have h_pushforward_null : rounded_mu Gδᶜ = 0 := by
      dsimp only [rounded_mu, robust_projection_main.pushforwardRound]
      rw [Measure.map_apply (robust_projection_main.measurable_roundToDeltaGrid δ) hGδc_meas]
      exact h_null
    have h_ae : Gδ ∈ MeasureTheory.ae rounded_mu := by
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
    have h_factor : δ * (k : ℝ) - δ * (m : ℝ) = δ * ((k : ℝ) - (m : ℝ)) := by ring
    calc dist x y
      = dist (δ * (k : ℝ)) (δ * (m : ℝ)) := by rw [hkx, hmy]
    _ = |δ * (k : ℝ) - δ * (m : ℝ)| := by rw [Real.dist_eq]
    _ = |δ * ((k : ℝ) - (m : ℝ))| := by rw [h_factor]
    _ = |δ| * |(k : ℝ) - (m : ℝ)| := by rw [abs_mul]
    _ = δ * |(k : ℝ) - (m : ℝ)| := by rw [abs_of_pos hδ_pos]
    _ ≥ δ * 1 := by gcongr
    _ = δ := by ring

  let A : Finset ℝ := hGδ_finite.toFinset
  have hA_coe : (A : Set ℝ) = Gδ := by
    simp [A, hGδ_finite.coe_toFinset]

  have hA_sep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → dist x y ≥ δ := by
    intro x hx y hy hxy
    have hx' : x ∈ Gδ := by rw [←hA_coe]; exact hx
    have hy' : y ∈ Gδ := by rw [←hA_coe]; exact hy
    exact hGδ_sep x y hx' hy' hxy

  have hA_sub : (A : Set ℝ) ⊆ Set.Icc 0 1 := by
    rw [hA_coe]; exact hGδ_sub_Icc

  have hν_supp : rounded_mu.support ⊆ (A : Set ℝ) := by
    rw [hA_coe]; exact hGδ_supp

  have h_rounded_mass_one : rounded_mu Set.univ = 1 := by
    dsimp only [rounded_mu, robust_projection_main.pushforwardRound]
    rw [Measure.map_apply (robust_projection_main.measurable_roundToDeltaGrid δ) MeasurableSet.univ]
    <;> simp [measure_univ]
  letI : IsProbabilityMeasure rounded_mu := ⟨h_rounded_mass_one⟩

  let K : ℝ := (3 : ℝ) ^ (2 * κ) * δ ^ (-η_energy)
  have hK_pos : 0 < K := by positivity

  have h_energy_round : robust_projection_main.rieszEnergy (2 * κ) hδ_pos rounded_mu ≤
      ENNReal.ofReal K := by
    have h1 := robust_projection_main.rounded_energy_bound hδ_pos hκ_pos (ν := μ)
    calc robust_projection_main.rieszEnergy (2 * κ) hδ_pos rounded_mu
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (2 * κ)) * robust_projection_main.rieszEnergy (2 * κ) hδ_pos μ := h1
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (2 * κ)) * ENNReal.ofReal (δ ^ (-η_energy)) := by
        gcongr <;> exact h_energy
    _ = ENNReal.ofReal K := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl

  obtain ⟨S, hS_sub_A, hS_delta_set, hS_mass⟩ :=
    robust_projection_main.energy_to_large_mass_delta_set
      hδ_pos hδ_lt_one hδ_dyadic' hκ_pos hκ_le_one hK_pos
      hA_sep hA_sub hν_supp h_energy_round hδ_small

  have hS_sub_Gδ : (S : Set ℝ) ⊆ Gδ := by
    have h : (S : Set ℝ) ⊆ (A : Set ℝ) := hS_sub_A
    rw [hA_coe] at h
    exact h

  have hS_grid : (S : Set ℝ) ⊆ productLikeIntegerGrid δ :=
    subset_trans hS_sub_Gδ hGδ_grid

  have hS_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y ≥ δ := by
    intro x hx y hy hxy
    exact hA_sep x (hS_sub_A hx) y (hS_sub_A hy) hxy

  have hS_grid_int : ∀ x ∈ S, ∃ k : ℤ, x = δ * (k : ℝ) := by
    intro x hx
    exact hS_grid hx

  let A_cells : Set ℝ := rnd ⁻¹' (S : Set ℝ)
  let A_source : Set ℝ := μ.support ∩ A_cells

  have hS_meas : MeasurableSet (S : Set ℝ) := by
    exact Set.Finite.measurableSet (Finset.finite_toSet S)

  have hA_cells_mass : μ A_cells = rounded_mu (S : Set ℝ) :=
    robust_projection_main.grid_preimage_measure hS_meas

  have hA_source_eq : μ A_source = μ A_cells := by
    have h2 : A_source = μ.support ∩ A_cells := rfl
    rw [h2]
    have hA_cells_meas : MeasurableSet A_cells :=
      hS_meas.preimage (robust_projection_main.measurable_roundToDeltaGrid δ)
    have h_supp_meas : MeasurableSet μ.support := by
      have h_closed : IsClosed μ.support := by exact Measure.isClosed_support
      exact h_closed.measurableSet
    have h4 : μ (A_cells \ μ.support) = 0 := by
      have h5 : A_cells \ μ.support ⊆ (μ.support)ᶜ := by
        intro z hz; exact hz.2
      exact measure_mono_null h5 μ.measure_compl_support
    have h_comm : μ.support ∩ A_cells = A_cells ∩ μ.support := by
      ext z; simp [and_comm]
    rw [h_comm]
    have h5 : μ (A_cells ∩ μ.support) + μ (A_cells \ μ.support) = μ A_cells :=
      MeasureTheory.measure_inter_add_sdiff A_cells h_supp_meas
    rw [h4, add_zero] at h5
    exact h5

  have hA_source_mass : μ A_source ≥ ENNReal.ofReal (3 / 4 : ℝ) := by
    rw [hA_source_eq, hA_cells_mass]
    exact hS_mass

  have hA_source_sub_support : A_source ⊆ μ.support := by
    intro z hz; exact hz.1

  have hS_delta_set_C : IsRealDeltaSet δ κ C_extract (S : Set ℝ) :=
    isRealDeltaSet_mono_C hS_delta_set hC_extract_large

  have hA_cells_delta : IsRealDeltaSet δ κ (6 * C_extract) A_cells :=
    robust_projection_main.local_delta_set_transfer hδ_pos hS_grid hS_delta_set_C

  have h_cov1 : Nreal δ A_source ≤ 2 * Nreal δ (S : Set ℝ) := by
    have h1 : Nreal δ A_source ≤ Nreal δ A_cells := by
      apply robust_projection_main.Nreal_mono_local
      intro z hz; exact hz.2
    have h2 : Nreal δ A_cells ≤ 2 * ENat.toENNReal (S : Set ℝ).encard :=
      robust_projection_main.grid_preimage_covering_bound hδ_pos hS_grid
    have h3 : ENat.toENNReal (S : Set ℝ).encard ≤ Nreal δ (S : Set ℝ) :=
      robust_projection_main.grid_set_card_le_Ndelta hδ_pos hS_grid
    calc Nreal δ A_source
      ≤ Nreal δ A_cells := h1
    _ ≤ 2 * ENat.toENNReal (S : Set ℝ).encard := h2
    _ ≤ 2 * Nreal δ (S : Set ℝ) := by gcongr

  have h_cov2 : Nreal δ A_source ≤ Nreal δ μ.support :=
    robust_projection_main.Nreal_mono_local hA_source_sub_support

  exact ⟨rnd, S, A_cells, A_source, rounded_mu,
    rfl, rfl, hS_grid_int, hS_sep, hS_mass, rfl, rfl,
    hA_source_mass, hA_source_sub_support, hS_delta_set_C,
    hA_cells_delta, h_cov1, h_cov2, hS_sub_Gδ⟩

end ProductLikeIncidence.ProductReduction
