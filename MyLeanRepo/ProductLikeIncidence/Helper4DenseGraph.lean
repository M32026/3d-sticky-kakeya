module

/-
# Helper 4: Dense Graph Construction

Given the projectively normalized set E3'', rounded coordinate sets S1, S2,
and all necessary bounds, construct a dense graph Gamma ⊆ S1 × S2.

## Pipeline
1. `density_endgame_V4` — establish c_dense * N(S1) * N(S2) ≤ N(E3'')
   (uses Pbar_param for covering number bounds)
2. `phase3_4_integration` — construct dense graph Gamma from E3''
   (uses Pbar = Pbar_param ∪ Pbar' for third projection monotonicity)

## Outputs
- Gamma : Set (EuclideanSpace ℝ (Fin 2))
- hGamma_sub, hGamma_grid, hGamma_fin, hGamma_nonempty, hGamma_separated
- hGamma_density : (c_dense/4) * Nreal δ S1 * Nreal δ S2 ≤ Nreal δ Gamma
- hGamma_witness : ∀ g ∈ Gamma, ∃ z ∈ E3'', g = round(z)
- Third projection bound for Gamma

## Whiteprint node
`itr_dense_graph_construction`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.ProductLikeIncidence.WireBudgets
public import MyLeanRepo.ProductLikeIncidence.WireBudgetsV4
public import MyLeanRepo.ProductLikeIncidence.DensityApplicationV4
public import MyLeanRepo.ProductLikeIncidence.Phase3_4Integration
public import MyLeanRepo.ProductLikeIncidence.GridSeparatedCard
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal MeasureTheory Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Helper 4: Dense graph construction from normalized E3'' and rounded S1, S2.

Uses `Pbar_param` for the density theorem (size lower bound) and `Pbar`
(typically `Pbar_param ∪ Pbar'`) for phase3_4_integration (third projection
monotonicity).
-/
lemma dense_graph_helper
    {δ κ0 η η_work L_exp rho_sel rho_sep : ℝ}
    {C_extract : ℝ}
    -- Basic
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_dyadic : δ ∈ dyadicScales)
    (hη_pos : 0 < η)
    (hη_work_pos : 0 < η_work)
    (hη_work_eq_two : η_work = 2 * η)
    (hL_exp_pos : 0 < L_exp)
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_pos : 0 < rho_sep)
    -- Density constant
    (c_dense : ENNReal)
    (hc_dense_eq : c_dense = ENNReal.ofReal (δ ^ (3 * rho_sel + 2 * rho_sep + qAbsorb η_work + L_exp * η_work)))
    -- Occupancy bound constant
    {M_G_real : ℝ}
    (hM_G_pos : 0 < M_G_real)
    (hM_G_bound1024 : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep))
    -- Absorption threshold
    (hδ_small_absorb : δ ^ qAbsorb η_work ≤ 1 / (2 * 1024 * 6 * 6))
    -- Sets: Pbar_param for density, Pbar for graph construction (Pbar ⊇ Pbar_param)
    {Pbar_param Pbar E3' E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    -- Rounding
    (round : ℝ → ℝ)
    (hround_grid : ∀ x, round x ∈ productLikeIntegerGrid δ)
    (h_round_near : ∀ x, |x - round x| ≤ δ / 2)
    -- S1/S2 properties
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    (hS1_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract S1)
    (hS2_delta : IsProductLikeRealDeltaSCSet δ κ0 C_extract S2)
    -- S1/S2 finiteness and nonemptiness (from Helper 3)
    (hS1_finite : S1.Finite)
    (hS2_finite : S2.Finite)
    (hS1_nonempty : S1.Nonempty)
    (hS2_nonempty : S2.Nonempty)
    -- E3' properties
    (hE3'_finite : E3'.Finite)
    (hE3'_sub_Pbar : E3' ⊆ Pbar)
    (hPbar_bounded : IsBounded Pbar)
    (hPbar_param_sub_Pbar : Pbar_param ⊆ Pbar)
    -- Size: |E3'| ≥ δ^{3ρ_sel} · N(Pbar_param)
    (hE3'_size : ENat.toENNReal E3'.encard ≥
        ENNReal.ofReal (δ ^ (3 * rho_sel)) * ENat.toENNReal (dyadicCoveringNumber δ Pbar_param))
    -- E3'' properties
    (hE3''_sub : E3'' ⊆ E3')
    (hE3''_half : ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2)
    -- Occupancy for E3'
    (h_occupancy : ∀ Q, Q ∈ dyadicCubes 2 δ →
        ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal M_G_real)
    -- Projection bounds for E3' relative to Pbar_param
    (h_proj_x : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)))
    (h_proj_y : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)))
    -- S1/S2 covering bounds relative to projections
    (hS1_bound : Nreal δ S1 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3'))
    (hS2_bound : Nreal δ S2 ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3'))
    -- Third projection bound for E3' relative to Pbar
    (h_third_proj_E3' : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal)))
    -- Measure and mass
    {μE3' : Measure (EuclideanSpace ℝ (Fin 2))}
    [IsProbabilityMeasure μE3']
    (hE3''_mass : μE3' E3'' ≥ ENNReal.ofReal (1 / 2 : ℝ))
    (hE3''_round : ∀ p ∈ E3'', round (p 0) ∈ S1 ∧ round (p 1) ∈ S2) :
    ∃ (Gamma : Set (EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ Gamma, p 0 ∈ S1 ∧ p 1 ∈ S2) ∧
      (∀ p ∈ Gamma, ∀ i : Fin 2, ∃ k : ℤ, p i = δ * (k : ℝ)) ∧
      Gamma.Finite ∧
      Gamma.Nonempty ∧
      (∀ z ∈ Gamma, ∀ w ∈ Gamma, z ≠ w → dist z w ≥ δ) ∧
      ENat.toENNReal (dyadicCoveringNumber δ Gamma) ≥
        (c_dense / 4) * Nreal δ S1 * Nreal δ S2 ∧
      (∀ g ∈ Gamma, ∃ z ∈ E3'', g 0 = round (z 0) ∧ g 1 = round (z 1)) ∧
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
        3 * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) E3') ∧
      Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0 + p 1) Gamma) ≤
        3 * (ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) := by
  -- =====================================================================
  -- Density bound via density_endgame_V4
  -- =====================================================================
  have h_density_E3'' : c_dense * Nreal δ S1 * Nreal δ S2 ≤
      ENat.toENNReal (dyadicCoveringNumber δ E3'') := by
    rw [hc_dense_eq]
    exact density_endgame_V4
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hrho_sel_pos := hrho_sel_pos) (hrho_sep_pos := hrho_sep_pos)
      (hη_pos := hη_pos) (hη_work_pos := hη_work_pos)
      (hη_work_eq_two := hη_work_eq_two) (hL_exp_pos := hL_exp_pos)
      (hM_G_pos := hM_G_pos)
      (hM_G_bound1024 := hM_G_bound1024)
      (hδ_small_absorb := hδ_small_absorb)
      (hE3'_finite := hE3'_finite)
      (hE3'_size := hE3'_size)
      (hE3''_half := by simpa [div_eq_mul_inv] using hE3''_half)
      (hE3''_sub := hE3''_sub)
      (h_occupancy := h_occupancy)
      (h_proj_x := h_proj_x) (h_proj_y := h_proj_y)
      (hS1_bound := hS1_bound) (hS2_bound := hS2_bound)

  -- =====================================================================
  -- Construct Gamma via phase3_4_integration
  -- =====================================================================
  rcases phase3_4_integration
      (hδ_pos := hδ_pos) (hδ_dyadic := hδ_dyadic)
      (hE3'_finite := hE3'_finite)
      (hE3'_sub_Pbar := hE3'_sub_Pbar)
      (hPbar_bounded := hPbar_bounded)
      (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
      (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
      (hS1_delta := hS1_delta) (hS2_delta := hS2_delta)
      (hE3''_sub := hE3''_sub)
      (hE3''_mass := hE3''_mass)
      (hE3''_round := hE3''_round)
      (round := round) (hround_grid := hround_grid) (h_round_near := h_round_near)
      (c_dense := c_dense)
      (h_density_E3'' := h_density_E3'')
      (h_third_proj_E3' := h_third_proj_E3')
    with ⟨Gamma, hGamma_sub, hGamma_grid, hGamma_density, hGamma_third1, hGamma_third2, hGamma_witness⟩

  -- =====================================================================
  -- Finiteness of Gamma: map S1 × S2 into EuclideanSpace
  -- =====================================================================
  let f_prod : ℝ × ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun p => (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun i => if i = 0 then p.1 else p.2)
  have hGamma_fin : Gamma.Finite := by
    have h_sub : Gamma ⊆ f_prod '' (S1 ×ˢ S2) := by
      intro p hp
      have h := hGamma_sub p hp
      refine ⟨(p 0, p 1), ⟨h.1, h.2⟩, ?_⟩
      ext i; fin_cases i <;> simp [f_prod, WithLp.equiv_symm_apply]
    have h_prod_fin : (S1 ×ˢ S2).Finite := hS1_finite.prod hS2_finite
    exact (h_prod_fin.image f_prod).subset h_sub

  -- =====================================================================
  -- Nonemptiness of Gamma: density + positivity of Nreal
  -- =====================================================================
  have hNreal_pos : ∀ (A : Set ℝ), (realLineCopy A).Nonempty → 0 < Nreal δ A := by
    intro A hA
    have h2 : (dyadicCubesMeeting δ (realLineCopy A)).Nonempty := by
      rcases hA with ⟨p, hp⟩
      let k : Fin 1 → ℤ := fun i => Int.floor (p i / δ)
      have hk : ∀ i, p i ∈ Set.Ico (δ * (k i : ℝ)) (δ * ((k i : ℝ) + 1)) := by
        intro i
        have h4 : (k i : ℝ) ≤ p i / δ := Int.floor_le (p i / δ)
        have h5 : p i / δ < (k i : ℝ) + 1 := Int.lt_floor_add_one (p i / δ)
        have h6 : δ * (k i : ℝ) ≤ p i := by
          calc δ * (k i : ℝ) ≤ δ * (p i / δ) := by gcongr
            _ = p i := by field_simp [hδ_pos.ne'] <;> ring
        have h7 : p i < δ * ((k i : ℝ) + 1) := by
          calc p i = δ * (p i / δ) := by field_simp [hδ_pos.ne'] <;> ring
            _ < δ * ((k i : ℝ) + 1) := by gcongr
        exact ⟨h6, h7⟩
      let Q := dyadicCube δ k
      have hQ_in : Q ∈ dyadicCubes 1 δ := ⟨k, rfl⟩
      have hQ_meets : (Q ∩ realLineCopy A).Nonempty := ⟨p, hk, hp⟩
      exact ⟨Q, hQ_in, hQ_meets⟩
    have h3 : 0 < ENat.toENNReal (dyadicCoveringNumber δ (realLineCopy A)) := by
      have h4 : (dyadicCoveringNumber δ (realLineCopy A)) ≠ 0 := by
        intro h5
        have h6 : dyadicCoveringNumber δ (realLineCopy A) = 0 := h5
        rw [dyadicCoveringNumber] at h6
        have h7 : (dyadicCubesMeeting δ (realLineCopy A)) = ∅ := by
          simpa [Set.encard_eq_zero] using h6
        rw [h7] at h2
        simp at h2
      have h5 : 0 < dyadicCoveringNumber δ (realLineCopy A) := by
        exact robust_projection.dyadic_covering_number_pos hδ_pos hA
      exact_mod_cast h5
    simpa [Nreal] using h3
  have hS1_re_nonempty : (realLineCopy S1).Nonempty := hS1_delta.2.1
  have hS2_re_nonempty : (realLineCopy S2).Nonempty := hS2_delta.2.1
  have hS1_pos : 0 < Nreal δ S1 := hNreal_pos S1 hS1_re_nonempty
  have hS2_pos : 0 < Nreal δ S2 := hNreal_pos S2 hS2_re_nonempty
  have hGamma_nonempty : Gamma.Nonempty := by
    by_contra h
    have h_empty : Gamma = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    have h_dens' := hGamma_density
    have h_zero : ENat.toENNReal (dyadicCoveringNumber δ Gamma) = 0 := by
      rw [h_empty]
      simp [dyadicCoveringNumber, dyadicCubesMeeting]
    rw [h_zero] at h_dens'
    have h_pos : 0 < (c_dense / 4) * Nreal δ S1 * Nreal δ S2 := by
      have hcd : 0 < c_dense := by
        rw [hc_dense_eq]; exact ENNReal.ofReal_pos.mpr (by positivity)
      have h1 : 0 < c_dense / 4 := by
        apply ENNReal.div_pos hcd.ne'
        norm_num
      positivity
    exact not_le.mpr h_pos h_dens'

  -- =====================================================================
  -- δ-separation of Gamma: coordinate difference ≥ δ implies dist ≥ δ
  -- =====================================================================
  have h_coord_le_dist : ∀ (z w : EuclideanSpace ℝ (Fin 2)) (i : Fin 2),
      |z i - w i| ≤ dist z w := by
    intro z w i
    let x := z - w
    have h1 : |x i| ≤ ‖x‖ := by
      have h2 : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i
      have h3 : ‖x i‖ = |x i| := by
        simp [Real.norm_eq_abs]
      rw [h3] at h2
      exact h2
    have h9 : z i - w i = x i := by simp [x]
    have h10 : |z i - w i| = |x i| := by rw [h9]
    have h11 : dist z w = ‖x‖ := by simp [x, dist_eq_norm]
    rw [h10, h11]
    exact h1
  have hGamma_separated : ∀ z ∈ Gamma, ∀ w ∈ Gamma, z ≠ w → dist z w ≥ δ := by
    intro z hz w hw hne
    have hz1 : z 0 ∈ S1 := (hGamma_sub z hz).1
    have hz2 : z 1 ∈ S2 := (hGamma_sub z hz).2
    have hw1 : w 0 ∈ S1 := (hGamma_sub w hw).1
    have hw2 : w 1 ∈ S2 := (hGamma_sub w hw).2
    by_cases h : z 0 ≠ w 0
    · have hsep : |z 0 - w 0| ≥ δ := hS1_sep (z 0) hz1 (w 0) hw1 h
      have hdist : |z 0 - w 0| ≤ dist z w := h_coord_le_dist z w 0
      linarith
    · have h' : z 1 ≠ w 1 := by
        intro h2; apply hne; ext i; fin_cases i <;> tauto
      have hsep : |z 1 - w 1| ≥ δ := hS2_sep (z 1) hz2 (w 1) hw2 h'
      have hdist : |z 1 - w 1| ≤ dist z w := h_coord_le_dist z w 1
      linarith

  -- =====================================================================
  -- Package outputs
  -- =====================================================================
  exact ⟨Gamma, hGamma_sub, hGamma_grid, hGamma_fin, hGamma_nonempty,
    hGamma_separated, hGamma_density, hGamma_witness, hGamma_third1, hGamma_third2⟩

end ProductLikeIncidence.ProductReduction
