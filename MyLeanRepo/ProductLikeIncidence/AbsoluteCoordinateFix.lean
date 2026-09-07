module

/-
# Absolute Coordinate Bounds

Extracts the absolute-coordinate size bounds from the monolith proof.

Given:
- `Pbar` with lower bound `N(Pbar) ≥ (1/98)·δ^{-2s+9η/2}`
- `S1, S2` with strong upper bounds `N(S_i) ≤ 6·δ^{-α}·X` where `X = √N(Pbar)`
- Product lower bound `N(S1)·N(S2) ≥ (1/2)·δ^{3ρ_sel+qMassV4}·N(Pbar)`
- Absorption `2^20 ≤ δ^{-qAbsorb}`
- Exponent identities

Produces:
- `K_A` with comparability `N(S1) ≤ K_A·N(S2)` and vice versa
- `K_A ≤ δ^{-qKA}`
- Final size lower bounds `|S_i| ≥ δ^{-s+q_input}`

This is the "strong coordinate bounds" route from the monolith
(`IncidenceToRingProof_v2.lean`, lines ~3292–3542).

## Dependencies

- `K_A_from_common_scale_bounds` — `K_A_Wrapper`
- `dyadicCoveringNumber_realLineCopy` — grid-to-encard conversion
-/

public import MyLeanRepo.CoreDefinitions
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeIncidence.K_A_Wrapper
public import MyLeanRepo.ProductLikeIncidence.CardinalityLowerBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Bornology ENNReal Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- **Absolute coordinate bounds**: derive K_A comparability and final size
lower bounds from strong coordinate upper bounds and Pbar lower bound.

Sets `X := √N(Pbar)`. Derives individual lower bounds
`N(S_i) ≥ (1/12)·δ^{α+qMassV4+3ρ_sel}·X` from the product lower bound
and the opposite upper bound, then uses `K_A_from_common_scale_bounds`.

The Pbar lower bound `N(Pbar) ≥ (1/98)·δ^{-2s+9η/2}` gives
`X ≥ (1/√98)·δ^{-s+9η/4}`, which combined with the exponent identity
and absorption yields `|S_i| ≥ δ^{-s+q_input}`. -/
lemma absolute_coordinate_bounds
    {δ s η_work rho_sel α qMassV4 qAbsorb q_input qKA : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    -- Exponent non-negativity
    (hα_pos : 0 < α) (hrho_sel_pos : 0 < rho_sel)
    (hqMassV4_nonneg : 0 ≤ qMassV4) (hqAbsorb_nonneg : 0 ≤ qAbsorb)
    (hq_input_nonneg : 0 ≤ q_input) (hqKA_nonneg : 0 ≤ qKA)
    -- Exponent identities
    (h_exp_id : α + qMassV4 + 3 * rho_sel + 9 * η_work / 4 = q_input - qAbsorb / 2)
    (h_KA_id : 2 * α + qMassV4 + 3 * rho_sel + 2 * qAbsorb = qKA)
    -- Absorption: 2^20 ≤ δ^{-qAbsorb}
    (h_box_bound : (2 : ℝ) ^ 20 ≤ δ ^ (-qAbsorb))
    -- Pbar
    {Pbar : Set (EuclideanSpace ℝ (Fin 2))}
    (hPbar_fin : Nplane δ Pbar ≠ ⊤)
    (hPbar_pos : 0 < Nplane δ Pbar)
    (hPbar_lower : Nplane δ Pbar ≥
        (1 / 98 : ENNReal) * ENNReal.ofReal (δ ^ (-2 * s + 9 * η_work / 2)))
    -- S1, S2 grid property (for Nreal = encard conversion)
    {S1 S2 : Set ℝ}
    (hS1_grid : S1 ⊆ productLikeIntegerGrid δ)
    (hS2_grid : S2 ⊆ productLikeIntegerGrid δ)
    (hS1_finite : S1.Finite)
    (hS2_finite : S2.Finite)
    -- Strong upper bounds: N(S_i) ≤ 6 · δ^{-α} · X
    (hS1_upper : Nreal δ S1 ≤
        (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)))
    (hS2_upper : Nreal δ S2 ≤
        (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) *
          ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)))
    -- Product lower bound: N(S1)·N(S2) ≥ (1/2)·δ^{3ρ_sel+qMassV4}·N(Pbar)
    (h_product_lower : (1 / 2 : ENNReal) *
        ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar ≤
        Nreal δ S1 * Nreal δ S2) :
    ∃ (K_A : ENNReal),
      (Nreal δ S1 ≤ K_A * Nreal δ S2) ∧
      (Nreal δ S2 ≤ K_A * Nreal δ S1) ∧
      (1 ≤ K_A) ∧
      (K_A ≠ ⊤) ∧
      (K_A ≤ ENNReal.ofReal (δ ^ (-qKA))) ∧
      (ENat.toENNReal S1.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input))) ∧
      (ENat.toENNReal S2.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input))) := by

  let X : ENNReal := ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal))
  have hX_pos : 0 < X := by
    have h1 : 0 < (Nplane δ Pbar).toReal := ENNReal.toReal_pos hPbar_pos.ne' hPbar_fin
    have h2 : 0 < Real.sqrt ((Nplane δ Pbar).toReal) := Real.sqrt_pos.mpr h1
    exact ENNReal.ofReal_pos.mpr h2
  have hX_ne_top : X ≠ ⊤ := by simp [X]
  have hX_sq : X * X = Nplane δ Pbar := by
    have h_nonneg : 0 ≤ (Nplane δ Pbar).toReal := ENNReal.toReal_nonneg
    have h1 : X * X = ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal) ^ 2) := by
      simp only [X]
      rw [← ENNReal.ofReal_mul (show 0 ≤ Real.sqrt ((Nplane δ Pbar).toReal) from Real.sqrt_nonneg _)]
      <;> ring_nf
    rw [h1]
    have h2 : Real.sqrt ((Nplane δ Pbar).toReal) ^ 2 = (Nplane δ Pbar).toReal :=
      Real.sq_sqrt h_nonneg
    rw [h2, ENNReal.ofReal_toReal hPbar_fin]

  -- Nreal = encard for grid sets (also gives finiteness)
  have hNreal_S1_eq : Nreal δ S1 = ENat.toENNReal S1.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy S1) = S1.encard :=
      dyadicCoveringNumber_realLineCopy hδ_pos hS1_grid
    simpa [Nreal] using congr_arg ENat.toENNReal h1
  have hNreal_S2_eq : Nreal δ S2 = ENat.toENNReal S2.encard := by
    have h1 : dyadicCoveringNumber δ (productLikeRealLineCopy S2) = S2.encard :=
      dyadicCoveringNumber_realLineCopy hδ_pos hS2_grid
    simpa [Nreal] using congr_arg ENat.toENNReal h1
  have hN1_ne_top : Nreal δ S1 ≠ ⊤ := by
    rw [hNreal_S1_eq]
    simpa using hS1_finite.encard_lt_top.ne
  have hN2_ne_top : Nreal δ S2 ≠ ⊤ := by
    rw [hNreal_S2_eq]
    simpa using hS2_finite.encard_lt_top.ne

  -- Product lower in X² format
  have hN1_pos : 0 < Nreal δ S1 := by
    by_contra h
    have h' : Nreal δ S1 = 0 := by simpa using h
    rw [h'] at h_product_lower
    have h_simp : (0 : ENNReal) * Nreal δ S2 = 0 := by simp
    rw [h_simp] at h_product_lower
    have h5 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar ≤ 0 := h_product_lower
    have h6 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · positivity
    have h7 : ((1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar) = 0 := by
      exact le_zero_iff.mp h5
    have h8 : Nplane δ Pbar = 0 := (mul_eq_zero.mp h7).resolve_left h6
    exact hPbar_pos.ne' h8
  have hN2_pos : 0 < Nreal δ S2 := by
    by_contra h
    have h' : Nreal δ S2 = 0 := by simpa using h
    rw [h'] at h_product_lower
    have h_simp : Nreal δ S1 * (0 : ENNReal) = 0 := by simp
    rw [h_simp] at h_product_lower
    have h5 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar ≤ 0 := h_product_lower
    have h6 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) ≠ 0 := by
      apply mul_ne_zero
      · norm_num
      · positivity
    have h7 : ((1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar) = 0 := by
      exact le_zero_iff.mp h5
    have h8 : Nplane δ Pbar = 0 := (mul_eq_zero.mp h7).resolve_left h6
    exact hPbar_pos.ne' h8

  have h_product_lower_X : (1 / 2 : ENNReal) *
      ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * X * X ≤
      Nreal δ S1 * Nreal δ S2 := by
    have h3 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * (X * X) =
        (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * Nplane δ Pbar := by
      exact congr_arg (fun y => (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * y) hX_sq
    have h4 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * X * X =
        (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * (X * X) := by
      simp [mul_assoc]
    rw [h4, h3]
    exact h_product_lower

  -- Lower S1 using strong upper on S2
  have hS1_lower_K : (1 / 12 : ENNReal) *
      ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X ≤ Nreal δ S1 := by
    by_contra h
    have h' : Nreal δ S1 < (1 / 12 : ENNReal) *
        ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X := lt_of_not_ge h
    have h_contra : Nreal δ S1 * Nreal δ S2 <
        (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * X * X := by
      let A := (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X
      have h_step1 : Nreal δ S1 * Nreal δ S2 < A * Nreal δ S2 := by
        have h_comm1 : A * Nreal δ S2 = Nreal δ S2 * A := by ring
        have h_comm2 : Nreal δ S1 * Nreal δ S2 = Nreal δ S2 * Nreal δ S1 := by ring
        rw [h_comm1, h_comm2]
        have h_iff : Nreal δ S2 * Nreal δ S1 < Nreal δ S2 * A ↔ Nreal δ S1 < A :=
          ENNReal.mul_lt_mul_iff_right hN2_pos.ne' hN2_ne_top
        exact h_iff.mpr h'
      have h_step2 : A * Nreal δ S2 ≤
          A * ((6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) := by
        exact mul_le_mul_of_nonneg_left hS2_upper (by positivity)
      have h_step3 : A * ((6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) =
          (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * X * X := by
        dsimp only [A]
        have h_exp : δ ^ (α + qMassV4 + 3 * rho_sel) * δ ^ (-α) = δ ^ (3 * rho_sel + qMassV4) := by
          have h_exponent : (α + qMassV4 + 3 * rho_sel) + (-α) = 3 * rho_sel + qMassV4 := by linarith
          rw [← Real.rpow_add hδ_pos, h_exponent]
        have h_pos1 : 0 ≤ δ ^ (α + qMassV4 + 3 * rho_sel) := by positivity
        have h_ofReal : ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α)) =
            ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) := by
          have h_mul : ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α)) =
              ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel) * δ ^ (-α)) := by
            rw [← ENNReal.ofReal_mul h_pos1]
          rw [h_mul]
          have h_arg : δ ^ (α + qMassV4 + 3 * rho_sel) * δ ^ (-α) = δ ^ (3 * rho_sel + qMassV4) := h_exp
          rw [h_arg]
        have h_const : (1 / 12 : ENNReal) * (6 : ENNReal) = (1 / 2 : ENNReal) := by
          have h_eq12 : (1 / 12 : ENNReal) = ENNReal.ofReal (1 / 12 : ℝ) := by
            have h_div : ENNReal.ofReal (1 / 12 : ℝ) = (1 : ENNReal) / (12 : ENNReal) := by
              rw [ENNReal.ofReal_div_of_pos (by norm_num)] <;> simp
            exact h_div.symm
          have h_eq6 : (6 : ENNReal) = ENNReal.ofReal (6 : ℝ) := by simp
          have h_eq2 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
            have h_div : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ENNReal) / (2 : ENNReal) := by
              rw [ENNReal.ofReal_div_of_pos (by norm_num)] <;> simp
            exact h_div.symm
          rw [h_eq12, h_eq6, h_eq2]
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          norm_num
        set u := (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) with hu
        set w := (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) with hw
        have h_main : u * X * (w * X) = (u * w) * (X * X) := by
          exact mul_mul_mul_comm u X w X
        have h_ac : u * w = (1 / 12 : ENNReal) * (6 : ENNReal) *
            (ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α))) := by
          dsimp only [u, w]
          exact mul_mul_mul_comm (1 / 12 : ENNReal) (ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel))) (6 : ENNReal) (ENNReal.ofReal (δ ^ (-α)))
        have h_rearr : (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X *
                ((6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) =
            (1 / 12 : ENNReal) * (6 : ENNReal) *
              (ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α))) * X * X := by
          rw [h_main, h_ac]
          <;> simp [mul_assoc]
        rw [h_rearr]
        rw [h_const, h_ofReal] <;> simp [mul_assoc]
      rw [h_step3] at h_step2
      exact lt_of_lt_of_le h_step1 h_step2
    exact not_le.mpr h_contra h_product_lower_X

  -- Lower S2 (symmetric)
  have hS2_lower_K : (1 / 12 : ENNReal) *
      ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X ≤ Nreal δ S2 := by
    by_contra h
    have h' : Nreal δ S2 < (1 / 12 : ENNReal) *
        ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X := lt_of_not_ge h
    have h_contra : Nreal δ S1 * Nreal δ S2 <
        (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * X * X := by
      let A := (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X
      have h_step1 : Nreal δ S1 * Nreal δ S2 < Nreal δ S1 * A := by
        have h_iff : Nreal δ S1 * Nreal δ S2 < Nreal δ S1 * A ↔ Nreal δ S2 < A :=
          ENNReal.mul_lt_mul_iff_right hN1_pos.ne' hN1_ne_top
        exact h_iff.mpr h'
      have h_step2 : Nreal δ S1 * A ≤
          ((6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) * A := by
        exact mul_le_mul_of_nonneg_right hS1_upper (by positivity)
      have h_step3 : ((6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) * A =
          (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) * X * X := by
        dsimp only [A]
        have h_exp : δ ^ (α + qMassV4 + 3 * rho_sel) * δ ^ (-α) = δ ^ (3 * rho_sel + qMassV4) := by
          have h_exponent : (α + qMassV4 + 3 * rho_sel) + (-α) = 3 * rho_sel + qMassV4 := by linarith
          rw [← Real.rpow_add hδ_pos, h_exponent]
        have h_pos1 : 0 ≤ δ ^ (α + qMassV4 + 3 * rho_sel) := by positivity
        have h_pos2 : 0 ≤ δ ^ (-α) := by positivity
        have h_ofReal : ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α)) =
            ENNReal.ofReal (δ ^ (3 * rho_sel + qMassV4)) := by
          have h_mul : ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α)) =
              ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel) * δ ^ (-α)) := by
            rw [← ENNReal.ofReal_mul h_pos1]
          rw [h_mul]
          have h_arg : δ ^ (α + qMassV4 + 3 * rho_sel) * δ ^ (-α) = δ ^ (3 * rho_sel + qMassV4) := h_exp
          rw [h_arg]
        have h_const : (1 / 12 : ENNReal) * (6 : ENNReal) = (1 / 2 : ENNReal) := by
          have h_eq12 : (1 / 12 : ENNReal) = ENNReal.ofReal (1 / 12 : ℝ) := by
            have h_div : ENNReal.ofReal (1 / 12 : ℝ) = (1 : ENNReal) / (12 : ENNReal) := by
              rw [ENNReal.ofReal_div_of_pos (by norm_num)] <;> simp
            exact h_div.symm
          have h_eq6 : (6 : ENNReal) = ENNReal.ofReal (6 : ℝ) := by simp
          have h_eq2 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
            have h_div : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ENNReal) / (2 : ENNReal) := by
              rw [ENNReal.ofReal_div_of_pos (by norm_num)] <;> simp
            exact h_div.symm
          rw [h_eq12, h_eq6, h_eq2]
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          norm_num
        set c := (6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) with hc
        set a := (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) with ha
        have h_comm : (c * X) * (a * X) = (a * X) * (c * X) := mul_comm _ _
        have h_main : (a * X) * (c * X) = (a * c) * (X * X) := by
          exact mul_mul_mul_comm a X c X
        have h_ac : a * c = (1 / 12 : ENNReal) * (6 : ENNReal) *
            (ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α))) := by
          dsimp only [a, c]
          exact mul_mul_mul_comm (1 / 12 : ENNReal) (ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel))) (6 : ENNReal) (ENNReal.ofReal (δ ^ (-α)))
        have h_rearr : ((6 : ENNReal) * ENNReal.ofReal (δ ^ (-α)) * X) *
                ((1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * X) =
            (1 / 12 : ENNReal) * (6 : ENNReal) *
              (ENNReal.ofReal (δ ^ (α + qMassV4 + 3 * rho_sel)) * ENNReal.ofReal (δ ^ (-α))) * X * X := by
          rw [h_comm, h_main, h_ac]
          <;> simp [mul_assoc]
        rw [h_rearr]
        rw [h_const, h_ofReal] <;> simp [mul_assoc]
      rw [h_step3] at h_step2
      exact lt_of_lt_of_le h_step1 h_step2
    exact not_le.mpr h_contra h_product_lower_X

  -- K_A via common-scale bounds
  have h_absorb_K : (6 : ENNReal) ≤
      (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (-(2 * qAbsorb))) := by
    have h1 : (72 : ℝ) ≤ δ ^ (-(2 * qAbsorb)) := by
      have h2 : (2 : ℝ) ^ 20 ≤ δ ^ (-qAbsorb) := h_box_bound
      have h3 : ((2 : ℝ) ^ 20) ^ 2 ≤ (δ ^ (-qAbsorb)) ^ 2 := by gcongr
      have h4 : (δ ^ (-qAbsorb)) ^ 2 = δ ^ (-(2 * qAbsorb)) := by
        have h41 : (δ ^ (-qAbsorb)) ^ 2 = (δ ^ (-qAbsorb)) * (δ ^ (-qAbsorb)) := by
          simp [pow_two]
        rw [h41]
        have h42 : (δ ^ (-qAbsorb)) * (δ ^ (-qAbsorb)) = δ ^ ((-qAbsorb) + (-qAbsorb)) := by
          rw [← Real.rpow_add hδ_pos]
        rw [h42]
        have h43 : (-qAbsorb) + (-qAbsorb) = -(2 * qAbsorb) := by ring
        rw [h43]
      rw [h4] at h3
      have h5 : (72 : ℝ) ≤ ((2 : ℝ) ^ 20) ^ 2 := by norm_num
      exact le_trans h5 h3
    have h6 : (6 : ENNReal) ≤ (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (-(2 * qAbsorb))) := by
      have h_eq12 : (1 / 12 : ENNReal) = ENNReal.ofReal (1 / 12 : ℝ) := by
        have h_div : ENNReal.ofReal (1 / 12 : ℝ) = (1 : ENNReal) / (12 : ENNReal) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)] <;> simp
        exact h_div.symm
      have h_pos : 0 ≤ (1 / 12 : ℝ) := by norm_num
      have h7 : (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ (-(2 * qAbsorb))) =
          ENNReal.ofReal ((1 / 12 : ℝ) * δ ^ (-(2 * qAbsorb))) := by
        rw [h_eq12]
        rw [← ENNReal.ofReal_mul h_pos]
        <;> rfl
      rw [h7]
      have h8 : (6 : ℝ) ≤ (1 / 12 : ℝ) * δ ^ (-(2 * qAbsorb)) := by linarith
      have h6_eq : (6 : ENNReal) = ENNReal.ofReal (6 : ℝ) := by simp
      rw [h6_eq]
      exact ENNReal.ofReal_le_ofReal h8
    exact h6

  have h_KA_exp_nonpos : (-α) - (α + qMassV4 + 3 * rho_sel) - (2 * qAbsorb) ≤ 0 := by
    have h : (-α) - (α + qMassV4 + 3 * rho_sel) - (2 * qAbsorb) = -qKA := by
      rw [← h_KA_id] <;> ring
    rw [h]
    exact neg_nonpos.mpr hqKA_nonneg

  rcases K_A_from_common_scale_bounds
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (h_exp_nonpos := h_KA_exp_nonpos)
      (hX_pos := hX_pos) (hX_ne_top := hX_ne_top)
      (C_upper := (6 : ENNReal)) (C_lower := (1 / 12 : ENNReal))
      (hC_lower_pos := by norm_num) (hC_lower_ne_top := by simp)
      (h_absorb := h_absorb_K)
      (hS1_upper := hS1_upper) (hS2_upper := hS2_upper)
      (hS1_lower := hS1_lower_K) (hS2_lower := hS2_lower_K)
    with ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top, hK_A_le⟩

  have h_KA_exp_eq : (-α) - (α + qMassV4 + 3 * rho_sel) - (2 * qAbsorb) = -qKA := by
    rw [← h_KA_id] <;> ring

  -- X lower bound from Pbar lower bound
  let inv_sqrt98 : ENNReal := ENNReal.ofReal (1 / Real.sqrt 98)
  have hX_lower : X ≥ inv_sqrt98 * ENNReal.ofReal (δ ^ (-s + 9 * η_work / 4)) := by
    have h_pos_exp : 0 ≤ δ ^ (-2 * s + 9 * η_work / 2) := by positivity
    have h2 : (Nplane δ Pbar).toReal ≥ (1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2) := by
      have h3 := ENNReal.toReal_mono hPbar_fin hPbar_lower
      have h4 : ((1 / 98 : ENNReal) * ENNReal.ofReal (δ ^ (-2 * s + 9 * η_work / 2))).toReal =
          (1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2) := by
        rw [ENNReal.toReal_mul]
        have h41 : (1 / 98 : ENNReal).toReal = (1 / 98 : ℝ) := by
          simp [ENNReal.toReal_div] <;> norm_num
        rw [h41, ENNReal.toReal_ofReal h_pos_exp] <;> ring
      rw [h4] at h3
      exact h3
    have h4 : Real.sqrt ((Nplane δ Pbar).toReal) ≥
        Real.sqrt ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) := Real.sqrt_le_sqrt h2
    have h_sqrt_rpow : ∀ (e : ℝ), Real.sqrt (δ ^ e) = δ ^ (e / 2) := by
      intro e
      have hδ_nonneg : 0 ≤ δ := by linarith
      have h1 : Real.sqrt (δ ^ e) = (δ ^ e) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h1]
      have h2 : (δ ^ e) ^ (1 / 2 : ℝ) = δ ^ (e * (1 / 2 : ℝ)) := by
        exact (Real.rpow_mul hδ_nonneg e (1 / 2 : ℝ)).symm
      rw [h2]
      have h3 : e * (1 / 2 : ℝ) = e / 2 := by ring
      rw [h3]
    have h5 : Real.sqrt ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) =
        (1 / Real.sqrt 98) * δ ^ (-s + 9 * η_work / 4) := by
      have h_pos1 : 0 ≤ (1 / 98 : ℝ) := by norm_num
      have h_sqrt98 : Real.sqrt (1 / 98 : ℝ) = 1 / Real.sqrt 98 := by
        rw [Real.sqrt_div (by norm_num)] <;> simp
      have h_exp : (-2 * s + 9 * η_work / 2) / 2 = -s + 9 * η_work / 4 := by ring
      have h_step1 : Real.sqrt ((1 / 98 : ℝ) * δ ^ (-2 * s + 9 * η_work / 2)) =
          Real.sqrt (1 / 98 : ℝ) * Real.sqrt (δ ^ (-2 * s + 9 * η_work / 2)) := by
        rw [Real.sqrt_mul h_pos1]
      rw [h_step1, h_sqrt_rpow (-2 * s + 9 * η_work / 2), h_sqrt98, h_exp]
    rw [h5] at h4
    have h6 : Real.sqrt ((Nplane δ Pbar).toReal) ≥
        (1 / Real.sqrt 98) * δ ^ (-s + 9 * η_work / 4) := h4
    have h7 : X = ENNReal.ofReal (Real.sqrt ((Nplane δ Pbar).toReal)) := by simp [X]
    rw [h7]
    have h8 : 0 ≤ (1 / Real.sqrt 98) * δ ^ (-s + 9 * η_work / 4) := by positivity
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h6

  -- Constant absorption: (1/12)·(1/√98)·δ^{-qAbsorb/2} ≥ 1
  have h_const_absorb : ((1 / 12 : ENNReal) * inv_sqrt98) *
      ENNReal.ofReal (δ ^ (-qAbsorb / 2)) ≥ 1 := by
    have h_sqrt_rpow : ∀ (e : ℝ), Real.sqrt (δ ^ e) = δ ^ (e / 2) := by
      intro e
      have hδ_nonneg : 0 ≤ δ := by linarith
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδ_nonneg] <;> ring_nf
    have h1 : (2 : ℝ) ^ 10 ≤ δ ^ (-qAbsorb / 2) := by
      have h2 : (2 : ℝ) ^ 20 ≤ δ ^ (-qAbsorb) := h_box_bound
      have h3 : Real.sqrt ((2 : ℝ) ^ 20) ≤ Real.sqrt (δ ^ (-qAbsorb)) := Real.sqrt_le_sqrt h2
      have h4 : Real.sqrt ((2 : ℝ) ^ 20) = (2 : ℝ) ^ 10 := by norm_num
      have h5 : Real.sqrt (δ ^ (-qAbsorb)) = δ ^ (-qAbsorb / 2) := h_sqrt_rpow (-qAbsorb)
      rw [h4, h5] at h3; exact h3
    have h6 : (12 : ℝ) * Real.sqrt 98 ≤ (2 : ℝ) ^ 10 := by
      have h_sqrt98_le : Real.sqrt 98 ≤ 10 := by
        rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
      calc
        (12 : ℝ) * Real.sqrt 98 ≤ (12 : ℝ) * 10 := by gcongr
        _ = 120 := by norm_num
        _ ≤ (2 : ℝ) ^ 10 := by norm_num
    have h7 : (12 : ℝ) * Real.sqrt 98 ≤ δ ^ (-qAbsorb / 2) := le_trans h6 h1
    have h9 : 0 < (12 : ℝ) * Real.sqrt 98 := by positivity
    have h8 : ((1 : ℝ) / 12) * (1 / Real.sqrt 98) * δ ^ (-qAbsorb / 2) ≥ 1 := by
      have h10 : ((1 : ℝ) / 12) * (1 / Real.sqrt 98) = 1 / ((12 : ℝ) * Real.sqrt 98) := by ring
      rw [h10]
      have h11 : 1 / ((12 : ℝ) * Real.sqrt 98) * δ ^ (-qAbsorb / 2) ≥
          1 / ((12 : ℝ) * Real.sqrt 98) * ((12 : ℝ) * Real.sqrt 98) := by
        gcongr
      have h12 : 1 / ((12 : ℝ) * Real.sqrt 98) * ((12 : ℝ) * Real.sqrt 98) = 1 := by
        field_simp [h9.ne'] <;> ring
      rw [h12] at h11
      exact h11
    have h_pos3 : 0 ≤ ((1 : ℝ) / 12) * (1 / Real.sqrt 98) * δ ^ (-qAbsorb / 2) := by positivity
    have h13 : ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (-qAbsorb / 2)) =
        ENNReal.ofReal (((1 : ℝ) / 12) * (1 / Real.sqrt 98) * δ ^ (-qAbsorb / 2)) := by
      simp [inv_sqrt98, ENNReal.ofReal_mul] <;> ring
    rw [h13]
    have h_one : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h_one]
    exact ENNReal.ofReal_le_ofReal h8

  -- Helper: combine ofReal powers
  have h_combine_powers : ∀ (a b : ℝ),
      ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b) = ENNReal.ofReal (δ ^ (a + b)) := by
    intro a b
    have h_posa : 0 ≤ δ ^ a := by positivity
    have h_posb : 0 ≤ δ ^ b := by positivity
    have h1 : ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b) = ENNReal.ofReal (δ ^ a * δ ^ b) := by
      rw [← ENNReal.ofReal_mul h_posa]
    rw [h1]
    have h2 : δ ^ a * δ ^ b = δ ^ (a + b) := by
      rw [← Real.rpow_add hδ_pos] <;> ring
    rw [h2]

  -- Final S1 lower bound
  have hS1_lower : ENat.toENNReal S1.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)) := by
    have h_main : Nreal δ S1 ≥ ENNReal.ofReal (δ ^ (-s + q_input)) := by
      let a := α + qMassV4 + 3 * rho_sel
      let b := -s + 9 * η_work / 4
      have h_step1 : Nreal δ S1 ≥ (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * X := hS1_lower_K
      have h_step2 : (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * X ≥
          (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * (inv_sqrt98 * ENNReal.ofReal (δ ^ b)) := by gcongr
      have h_rearr : (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * (inv_sqrt98 * ENNReal.ofReal (δ ^ b)) =
          ((1 / 12 : ENNReal) * inv_sqrt98) * (ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b)) := by
        exact mul_mul_mul_comm (1 / 12 : ENNReal) (ENNReal.ofReal (δ ^ a)) inv_sqrt98 (ENNReal.ofReal (δ ^ b))
      have h_combine : ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b) = ENNReal.ofReal (δ ^ (a + b)) := h_combine_powers a b
      have h_exp_eq2 : a + b = q_input - qAbsorb / 2 - s := by
        dsimp only [a, b]
        linarith [h_exp_id]
      have h_final : ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (q_input - qAbsorb / 2 - s)) =
          ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (-qAbsorb / 2)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
        have h_pos1 : 0 ≤ δ ^ (-qAbsorb / 2) := by positivity
        have h_pos2 : 0 ≤ δ ^ (-s + q_input) := by positivity
        have h3 : δ ^ (q_input - qAbsorb / 2 - s) = δ ^ (-qAbsorb / 2) * δ ^ (-s + q_input) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
        have h4 : ENNReal.ofReal (δ ^ (q_input - qAbsorb / 2 - s)) =
            ENNReal.ofReal (δ ^ (-qAbsorb / 2)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
          rw [h3, ENNReal.ofReal_mul h_pos1]
        rw [h4]
        <;> simp [mul_assoc]
      calc Nreal δ S1
        ≥ (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * X := h_step1
      _ ≥ (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * (inv_sqrt98 * ENNReal.ofReal (δ ^ b)) := h_step2
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * (ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b)) := h_rearr
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (a + b)) := by rw [h_combine]
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (q_input - qAbsorb / 2 - s)) := by rw [h_exp_eq2]
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (-qAbsorb / 2)) * ENNReal.ofReal (δ ^ (-s + q_input)) := h_final
      _ ≥ ENNReal.ofReal (δ ^ (-s + q_input)) := by
        have h : ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (-qAbsorb / 2)) ≥ 1 := h_const_absorb
        exact le_mul_of_one_le_left' h
    rw [hNreal_S1_eq] at h_main
    exact h_main

  -- Final S2 lower bound (symmetric)
  have hS2_lower : ENat.toENNReal S2.encard ≥ ENNReal.ofReal (δ ^ (-s + q_input)) := by
    have h_main : Nreal δ S2 ≥ ENNReal.ofReal (δ ^ (-s + q_input)) := by
      let a := α + qMassV4 + 3 * rho_sel
      let b := -s + 9 * η_work / 4
      have h_step1 : Nreal δ S2 ≥ (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * X := hS2_lower_K
      have h_step2 : (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * X ≥
          (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * (inv_sqrt98 * ENNReal.ofReal (δ ^ b)) := by gcongr
      have h_rearr : (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * (inv_sqrt98 * ENNReal.ofReal (δ ^ b)) =
          ((1 / 12 : ENNReal) * inv_sqrt98) * (ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b)) := by
        exact mul_mul_mul_comm (1 / 12 : ENNReal) (ENNReal.ofReal (δ ^ a)) inv_sqrt98 (ENNReal.ofReal (δ ^ b))
      have h_combine : ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b) = ENNReal.ofReal (δ ^ (a + b)) := h_combine_powers a b
      have h_exp_eq2 : a + b = q_input - qAbsorb / 2 - s := by
        dsimp only [a, b]
        linarith [h_exp_id]
      have h_final : ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (q_input - qAbsorb / 2 - s)) =
          ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (-qAbsorb / 2)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
        have h_pos1 : 0 ≤ δ ^ (-qAbsorb / 2) := by positivity
        have h_pos2 : 0 ≤ δ ^ (-s + q_input) := by positivity
        have h3 : δ ^ (q_input - qAbsorb / 2 - s) = δ ^ (-qAbsorb / 2) * δ ^ (-s + q_input) := by
          rw [← Real.rpow_add hδ_pos] <;> ring_nf
        have h4 : ENNReal.ofReal (δ ^ (q_input - qAbsorb / 2 - s)) =
            ENNReal.ofReal (δ ^ (-qAbsorb / 2)) * ENNReal.ofReal (δ ^ (-s + q_input)) := by
          rw [h3, ENNReal.ofReal_mul h_pos1]
        rw [h4]
        <;> simp [mul_assoc]
      calc Nreal δ S2
        ≥ (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * X := h_step1
      _ ≥ (1 / 12 : ENNReal) * ENNReal.ofReal (δ ^ a) * (inv_sqrt98 * ENNReal.ofReal (δ ^ b)) := h_step2
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * (ENNReal.ofReal (δ ^ a) * ENNReal.ofReal (δ ^ b)) := h_rearr
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (a + b)) := by rw [h_combine]
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (q_input - qAbsorb / 2 - s)) := by rw [h_exp_eq2]
      _ = ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (-qAbsorb / 2)) * ENNReal.ofReal (δ ^ (-s + q_input)) := h_final
      _ ≥ ENNReal.ofReal (δ ^ (-s + q_input)) := by
        have h : ((1 / 12 : ENNReal) * inv_sqrt98) * ENNReal.ofReal (δ ^ (-qAbsorb / 2)) ≥ 1 := h_const_absorb
        exact le_mul_of_one_le_left' h
    rw [hNreal_S2_eq] at h_main
    exact h_main

  exact ⟨K_A, hS1_le_S2, hS2_le_S1, hK_A_ge_one, hK_A_ne_top,
    by rw [h_KA_exp_eq] at hK_A_le; exact hK_A_le, hS1_lower, hS2_lower⟩

end ProductLikeIncidence.ProductReduction
