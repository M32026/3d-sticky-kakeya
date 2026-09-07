module

/-
# Absolute Coordinate Wiring Adapter

Wires upstream pipeline outputs (GlueH3ToH4 + Phase0) into
`absolute_coordinate_bounds`.

## Dependencies
- `MyLeanRepo.ProductLikeIncidence.CubeCounting`
- `MyLeanRepo.ProductLikeIncidence.AbsoluteCoordinateFix`
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.CubeCounting
public import MyLeanRepo.ProductLikeIncidence.AbsoluteCoordinateFix
public import MyLeanRepo.OSWPrelude

@[expose] public section

set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

open Set ENNReal Bornology Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-! ## Product bound with absorption (coordinate-wise version) -/

/-- **Product bound wiring (coordinate-wise)**: derive the exact
`h_product_lower` needed by `absolute_coordinate_bounds` using the
coordinate-wise rounding variant.

Uses `product_lower_from_occupancy_coord` from CubeCounting.
Absorbs the factor 4 into `qMassV4` using `qMassV4 = 2*rho_sep + qAbsorb`
and the box bound `2^20 ≤ δ^{-qAbsorb}`. -/
lemma product_bound_wiring_coord
    {δ rho_sel rho_sep qAbsorb qMassV4 : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hqAbsorb_pos : 0 < qAbsorb)
    (hqMassV4_eq : qMassV4 = 2 * rho_sep + qAbsorb)
    (h_box_bound : (2 : ℝ) ^ 20 ≤ δ ^ (-qAbsorb))
    {E3'' Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    {S1 S2 : Set ℝ}
    {M_G : ENNReal}
    (hE3''_size : ENat.toENNReal E3''.encard ≥
        (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar)
    (hS1_finite : S1.Finite) (hS2_finite : S2.Finite)
    (hS1_grid : ∀ x ∈ S1, x ∈ productLikeIntegerGrid δ)
    (hS2_grid : ∀ x ∈ S2, x ∈ productLikeIntegerGrid δ)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    (hE3''_finite : E3''.Finite)
    (h_occupancy : ∀ Q ∈ dyadicCubes 2 δ,
        ENat.toENNReal (E3'' ∩ Q).encard ≤ M_G)
    (hM_G_bound : M_G ≤ ENNReal.ofReal (1024 * δ ^ (-2 * rho_sep)))
    (round_fun : ℝ → ℝ)
    (h_round_near : ∀ z, |z - round_fun z| ≤ δ / 2)
    (h_round_image : ∀ p ∈ E3'', round_fun (p 0) ∈ S1 ∧ round_fun (p 1) ∈ S2) :
    (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar ≤
        Nreal δ S1 * Nreal δ S2 := by
  have h_product : Nreal δ S1 * Nreal δ S2 ≥
      ENat.toENNReal E3''.encard / (4 * M_G) :=
    product_lower_from_occupancy_coord
      (hδ_pos := hδ_pos)
      (hE3''_finite := hE3''_finite)
      (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
      (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
      (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
      (h_occupancy := h_occupancy)
      (round_fun := round_fun)
      (h_round_near := h_round_near)
      (h_round_image := h_round_image)
  have h4096_le : (4096 : ℝ) ≤ δ ^ (-qAbsorb) := by
    have h1 : (4096 : ℝ) ≤ (2 : ℝ)^20 := by norm_num
    exact le_trans h1 h_box_bound
  have h_pos_x : 0 ≤ (1024 * δ ^ (-2 * rho_sep)) := by positivity
  have h3 : (4 : ENNReal) * ENNReal.ofReal (1024 * δ ^ (-2 * rho_sep)) =
      ENNReal.ofReal (4096 * δ ^ (-2 * rho_sep)) := by
    have h_eq : ENNReal.ofReal (4 * (1024 * δ ^ (-2 * rho_sep))) =
        ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (1024 * δ ^ (-2 * rho_sep)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
    have h44 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
    have h_goal : (4 : ENNReal) * ENNReal.ofReal (1024 * δ ^ (-2 * rho_sep)) =
        ENNReal.ofReal (4 * (1024 * δ ^ (-2 * rho_sep))) := by
      rw [h44, ← h_eq]
    rw [h_goal]
    congr 1
    <;> ring
  have h4 : ENNReal.ofReal (4096 * δ ^ (-2 * rho_sep)) ≤ ENNReal.ofReal (δ ^ (-qMassV4)) := by
    apply ENNReal.ofReal_le_ofReal
    have h5 : qMassV4 = 2 * rho_sep + qAbsorb := hqMassV4_eq
    rw [h5]
    have h6 : (4096 : ℝ) * δ ^ (-2 * rho_sep) ≤ δ ^ (-(2 * rho_sep + qAbsorb)) := by
      have h7 : (4096 : ℝ) ≤ δ ^ (-qAbsorb) := h4096_le
      have h8 : (4096 : ℝ) * δ ^ (-2 * rho_sep) ≤ δ ^ (-qAbsorb) * δ ^ (-2 * rho_sep) := by gcongr
      have h9 : δ ^ (-qAbsorb) * δ ^ (-2 * rho_sep) = δ ^ (-(2 * rho_sep + qAbsorb)) := by
        rw [← Real.rpow_add hδ_pos] <;> ring_nf
      rw [h9] at h8; exact h8
    exact h6
  have h4MG : 4 * M_G ≤ ENNReal.ofReal (δ ^ (-qMassV4)) := by
    calc (4 : ENNReal) * M_G
      ≤ (4 : ENNReal) * ENNReal.ofReal (1024 * δ ^ (-2 * rho_sep)) := by gcongr
    _ = ENNReal.ofReal (4096 * δ ^ (-2 * rho_sep)) := h3
    _ ≤ ENNReal.ofReal (δ ^ (-qMassV4)) := h4
  have h_div : ENat.toENNReal E3''.encard / (4 * M_G) ≥
      ENat.toENNReal E3''.encard / ENNReal.ofReal (δ ^ (-qMassV4)) := by
    gcongr
  have h_pos_qMass : 0 < δ ^ (-qMassV4) := by positivity
  have h_inv : (ENNReal.ofReal (δ ^ (-qMassV4)))⁻¹ = ENNReal.ofReal (δ ^ qMassV4) := by
    have h_pos1 : 0 < δ ^ (-qMassV4) := h_pos_qMass
    have h_eq : (δ ^ (-qMassV4))⁻¹ = δ ^ qMassV4 := by
      have h_mul : δ ^ (-qMassV4) * δ ^ qMassV4 = 1 := by
        rw [← Real.rpow_add hδ_pos]
        have h_sum : (-qMassV4) + qMassV4 = 0 := by ring
        rw [h_sum]; simp
      exact inv_eq_of_mul_eq_one_right h_mul
    have h_enn : (ENNReal.ofReal (δ ^ (-qMassV4)))⁻¹ =
        ENNReal.ofReal ((δ ^ (-qMassV4))⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos h_pos1]
    rw [h_enn, h_eq]
  have h_div_eq : ENat.toENNReal E3''.encard / ENNReal.ofReal (δ ^ (-qMassV4)) =
      ENat.toENNReal E3''.encard * ENNReal.ofReal (δ ^ qMassV4) := by
    rw [div_eq_mul_inv, h_inv]
  have h_pos3 : 0 ≤ δ ^ (3 * rho_sel) := by positivity
  have h_pos4 : 0 ≤ δ ^ qMassV4 := by positivity
  have h_mul_exp : δ ^ (3 * rho_sel) * δ ^ qMassV4 = δ ^ (3 * rho_sel + qMassV4) := by
    rw [← Real.rpow_add hδ_pos]
  have h6 : ENNReal.ofReal (δ ^ (3 * rho_sel)) * ENNReal.ofReal (δ ^ qMassV4) =
      ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) := by
    rw [← ENNReal.ofReal_mul h_pos3, h_mul_exp]
  calc
    (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar
      = (1 / 2 : ENNReal) * (ENNReal.ofReal (δ ^ (3 * rho_sel)) * ENNReal.ofReal (δ ^ qMassV4)) * Nplane δ Pbar := by rw [h6]
    _ = ((1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar) * ENNReal.ofReal (δ ^ qMassV4) := by
      simp only [mul_assoc]
      <;> ac_rfl
    _ ≤ ENat.toENNReal E3''.encard * ENNReal.ofReal (δ ^ qMassV4) := by gcongr
    _ = ENat.toENNReal E3''.encard / ENNReal.ofReal (δ ^ (-qMassV4)) := by rw [h_div_eq]
    _ ≤ ENat.toENNReal E3''.encard / (4 * M_G) := h_div
    _ ≤ Nreal δ S1 * Nreal δ S2 := h_product

/-! ## Main wiring adapter -/

/-- **Absolute coordinate wiring adapter**: takes upstream pipeline outputs
and produces all inputs for `absolute_coordinate_bounds`.

Derives:
1. Strong upper bounds `N(S_i) ≤ 6·δ^{-α}·X` from projection + rounding bounds
2. Product lower bound via coordinate-wise cube counting + absorption
3. Calls `absolute_coordinate_bounds` to get K_A comparability and size bounds

Uses `qMassV4 = 2*rho_sep + qAbsorb` for constant absorption. -/
lemma absolute_coordinate_wiring
    {δ s η_work rho_sel rho_sep α qMassV4 qAbsorb q_input qKA : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    -- Exponent non-negativity
    (hα_pos : 0 < α) (hrho_sel_pos : 0 < rho_sel)
    (hrho_sep_nonneg : 0 ≤ rho_sep)
    (hqAbsorb_pos : 0 < qAbsorb)
    (hqMassV4_nonneg : 0 ≤ qMassV4)
    (hq_input_nonneg : 0 ≤ q_input) (hqKA_nonneg : 0 ≤ qKA)
    -- Exponent identities
    (hqMassV4_eq : qMassV4 = 2 * rho_sep + qAbsorb)
    (h_exp_id : α + qMassV4 + 3 * rho_sel + 9 * η_work / 4 = q_input - qAbsorb / 2)
    (h_KA_id : 2 * α + qMassV4 + 3 * rho_sel + 2 * qAbsorb = qKA)
    -- Absorption
    (h_box_bound : (2 : ℝ) ^ 20 ≤ δ ^ (-qAbsorb))
    -- Pbar (= Pbar_param)
    {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_fin : Nplane δ Pbar ≠ ⊤)
    (hPbar_pos : 0 < Nplane δ Pbar)
    (hPbar_lower : Nplane δ Pbar ≥
        (1 / 98 : ENNReal) * ENNReal.ofReal (δ ^ (-2 * s + 9 * η_work / 2)))
    -- S1, S2
    {S1 S2 : Set ℝ}
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    (hS1_finite : S1.Finite)
    (hS2_finite : S2.Finite)
    (hS1_sep : ∀ x ∈ S1, ∀ y ∈ S1, x ≠ y → |x - y| ≥ δ)
    (hS2_sep : ∀ x ∈ S2, ∀ y ∈ S2, x ≠ y → |x - y| ≥ δ)
    -- E3' and E3''
    {E3' E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    (hE3'_finite : E3'.Finite)
    (hE3''_finite : E3''.Finite)
    (hE3''_sub : E3'' ⊆ E3')
    (hE3'_size : ENat.toENNReal E3'.encard ≥
        ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar)
    (hE3''_half : ENat.toENNReal E3''.encard ≥ ENat.toENNReal E3'.encard / 2)
    -- Occupancy
    {M_G_real : ℝ}
    (hM_G_pos : 0 < M_G_real)
    (hM_G_bound : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep))
    (hE3'_occupancy : ∀ Q ∈ dyadicCubes 2 δ,
        ENat.toENNReal (E3' ∩ Q).encard ≤ ENNReal.ofReal M_G_real)
    -- Rounding
    (round_fun : ℝ → ℝ)
    (h_round_near : ∀ z, |z - round_fun z| ≤ δ / 2)
    (hE3''_round : ∀ p ∈ E3'', round_fun (p 0) ∈ S1 ∧ round_fun (p 1) ∈ S2)
    -- Projection bounds (factor 2)
    (h_proj1 : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)))
    (h_proj2 : Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3') ≤
        (2 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)))
    -- Rounding bounds (factor 3)
    (h_round1 : Nreal δ S1 ≤
        (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 0) E3'))
    (h_round2 : Nreal δ S2 ≤
        (3 : ENNReal) * Nreal δ (Set.image (fun p : EuclideanSpace ℝ (Fin 2) => p 1) E3')) :
    ∃ (K_A : ENNReal),
      (Nreal δ S1 ≤ K_A * Nreal δ S2) ∧
      (Nreal δ S2 ≤ K_A * Nreal δ S1) ∧
      (1 ≤ K_A) ∧
      (K_A ≠ ⊤) ∧
      (K_A ≤ ENNReal.ofReal (δ ^ (-qKA))) ∧
      (ENat.toENNReal S1.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input))) ∧
      (ENat.toENNReal S2.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input))) := by
  let X : ENNReal := ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal))
  let M_G : ENNReal := ENNReal.ofReal M_G_real

  -- Strong upper bounds: N(S_i) ≤ 6 · δ^{-α} · X
  have hS1_upper : Nreal δ S1 ≤ (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X := by
    calc Nreal δ S1
      ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p => p 0) E3') := h_round1
    _ ≤ (3 : ENNReal) * ((2 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) := by gcongr
    _ = (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
  have hS2_upper : Nreal δ S2 ≤ (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X := by
    calc Nreal δ S2
      ≤ (3 : ENNReal) * Nreal δ (Set.image (fun p => p 1) E3') := h_round2
    _ ≤ (3 : ENNReal) * ((2 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) := by gcongr
    _ = (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring

  -- E3'' size: |E3''| ≥ (1/2) · δ^{3ρ_sel} · N(Pbar)
  have hE3''_size : ENat.toENNReal E3''.encard ≥
      (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar := by
    calc ENat.toENNReal E3''.encard
      ≥ ENat.toENNReal E3'.encard / 2 := hE3''_half
    _ ≥ ((ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar) / 2) := by gcongr
    _ = (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar := by
      have h_eq : (ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar) / 2 =
          (1 / 2 : ENNReal) * (ENNReal.ofReal (δ ^ (3 * rho_sel)) * Nplane δ Pbar) := by
        simp [div_eq_mul_inv] <;> ring
      rw [h_eq] <;> simp [mul_assoc]

  -- E3'' occupancy from E3' occupancy
  have hE3''_occupancy : ∀ Q ∈ dyadicCubes 2 δ,
      ENat.toENNReal (E3'' ∩ Q).encard ≤ M_G := by
    intro Q hQ
    have h_sub : (E3'' ∩ Q) ⊆ (E3' ∩ Q) := by
      intro x hx; exact ⟨hE3''_sub hx.1, hx.2⟩
    have h1 : ENat.toENNReal (E3'' ∩ Q).encard ≤ ENat.toENNReal (E3' ∩ Q).encard := by
      exact ENat.toENNReal_mono (Set.encard_mono h_sub)
    have h2 := hE3'_occupancy Q hQ
    exact le_trans h1 h2

  -- M_G bound in ENNReal
  have hM_G_bound' : M_G ≤ ENNReal.ofReal (1024 * δ ^ (-2 * rho_sep)) := by
    have h1 : M_G_real ≤ 1024 * δ ^ (-2 * rho_sep) := hM_G_bound
    exact ENNReal.ofReal_le_ofReal h1

  -- Grid properties in ∀ form
  have hS1_grid' : ∀ x ∈ S1, x ∈ productLikeIntegerGrid δ := by
    intro x hx; exact hS1_grid hx
  have hS2_grid' : ∀ x ∈ S2, x ∈ productLikeIntegerGrid δ := by
    intro x hx; exact hS2_grid hx

  -- Product lower bound with absorption
  have h_product_lower : (1 / 2 : ENNReal) *
      ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar ≤
      Nreal δ S1 * Nreal δ S2 :=
    product_bound_wiring_coord
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hrho_sel_pos := hrho_sel_pos) (hrho_sep_nonneg := hrho_sep_nonneg)
      (hqAbsorb_pos := hqAbsorb_pos) (hqMassV4_eq := hqMassV4_eq)
      (h_box_bound := h_box_bound)
      (hE3''_size := hE3''_size)
      (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
      (hS1_grid := hS1_grid') (hS2_grid := hS2_grid')
      (hS1_sep := hS1_sep) (hS2_sep := hS2_sep)
      (hE3''_finite := hE3''_finite)
      (h_occupancy := hE3''_occupancy)
      (hM_G_bound := hM_G_bound')
      (round_fun := round_fun)
      (h_round_near := h_round_near)
      (h_round_image := hE3''_round)

  -- Call absolute_coordinate_bounds
  exact absolute_coordinate_bounds
    (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
    (hα_pos := hα_pos) (hrho_sel_pos := hrho_sel_pos)
    (hqMassV4_nonneg := hqMassV4_nonneg) (hqAbsorb_nonneg := le_of_lt hqAbsorb_pos)
    (hq_input_nonneg := hq_input_nonneg) (hqKA_nonneg := hqKA_nonneg)
    (h_exp_id := h_exp_id) (h_KA_id := h_KA_id)
    (h_box_bound := h_box_bound)
    (hPbar_fin := hPbar_fin) (hPbar_pos := hPbar_pos)
    (hPbar_lower := hPbar_lower)
    (hS1_grid := hS1_grid) (hS2_grid := hS2_grid)
    (hS1_finite := hS1_finite) (hS2_finite := hS2_finite)
    (hS1_upper := hS1_upper) (hS2_upper := hS2_upper)
    (h_product_lower := h_product_lower)

end ProductLikeIncidence.ProductReduction
