import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperCoarseRestore

/-!
# Uniform coarse-scale absorption for the paper four-call candidate

This is the coarse A-segment only.  It restores the candidate built directly
from `data.prepared.refined.shading`; no re-entry retention, preparation loss,
fine pullback, or root-family cardinality occurs here.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Total negative power in the exact coarse paper-candidate ledger. -/
noncomputable def proposition63FourCallPaperCoarseBurden
    (normalizationLoss internalLoss epsilon₁ angular floorLoss : ℝ) : ℝ :=
  normalizationLoss + 3 * internalLoss / 2 + 7 * epsilon₁ + angular + floorLoss

/-- The fixed coefficient left after the exact cell, cover, and geometric
constants have been separated from their powers of the runtime scale. -/
noncomputable def proposition63FourCallPaperCoarseCoefficient
    (coefficient : NNReal) : ENNReal :=
  1 + 1024 * ((1605264998400 : ENNReal) *
    (coefficient : ENNReal) ^ 3 + 2)

/-- Polynomial majorant for the coefficient used by coarse-A restoration. -/
theorem proposition63_four_call_paper_coarse_coefficient_le_cubic
    (coefficient : NNReal) (coefficient_one : 1 ≤ (coefficient : ℝ)) :
    proposition63FourCallPaperCoarseCoefficient coefficient ≤
      (1643791358363649 : ENNReal) * (coefficient : ENNReal) ^ 3 := by
  have coefficientOneENN : (1 : ENNReal) ≤ (coefficient : ENNReal) := by
    exact_mod_cast coefficient_one
  have cubeOne : (1 : ENNReal) ≤ (coefficient : ENNReal) ^ 3 := by
    simpa using pow_le_pow_left' coefficientOneENN 3
  have twoLeCube : (2 : ENNReal) ≤
      2 * (coefficient : ENNReal) ^ 3 := by
    simpa using mul_le_mul_left' cubeOne (2 : ENNReal)
  unfold proposition63FourCallPaperCoarseCoefficient
  calc
    (1 : ENNReal) + 1024 *
          ((1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 + 2) ≤
        (coefficient : ENNReal) ^ 3 + 1024 *
          ((1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 +
            2 * (coefficient : ENNReal) ^ 3) := by
      exact add_le_add cubeOne (mul_le_mul_left'
        (add_le_add_right twoLeCube
          ((1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3))
        (1024 : ENNReal))
    _ = (1643791358363649 : ENNReal) *
          (coefficient : ENNReal) ^ 3 := by ring

private theorem realRpowENN_sqrt
    {rho exponent : ℝ} (rho_pos : 0 < rho) :
    Kakeya.realRpowENN (Real.sqrt rho) exponent =
      Kakeya.realRpowENN rho (exponent / 2) := by
  simp only [Kakeya.realRpowENN, Real.sqrt_eq_rpow]
  congr 1
  calc
    (Real.rpow rho (1 / 2)).rpow exponent =
        Real.rpow rho ((1 / 2) * exponent) :=
      (Real.rpow_mul rho_pos.le _ _).symm
    _ = Real.rpow rho (exponent / 2) := by congr 1; ring

private theorem realRpowENN_inv
    {rho exponent : ℝ} (rho_pos : 0 < rho) :
    (Kakeya.realRpowENN rho exponent)⁻¹ =
      Kakeya.realRpowENN rho (-exponent) := by
  simp only [Kakeya.realRpowENN]
  calc
    (ENNReal.ofReal (Real.rpow rho exponent))⁻¹ =
        ENNReal.ofReal ((Real.rpow rho exponent)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos rho_pos exponent)).symm
    _ = ENNReal.ofReal (Real.rpow rho (-exponent)) :=
      congrArg ENNReal.ofReal (Real.rpow_neg rho_pos.le exponent).symm

private theorem proposition63_four_call_cell_floor_exact
    {rho sigma internalLoss floorLoss : ℝ} (rho_pos : 0 < rho) :
    ENNReal.ofReal
        (proposition63_four_call_cell_volume_floor_choice rho_pos
          (Real.sqrt_pos.2 rho_pos) (sigma := sigma)
          (outputLoss := internalLoss) (floorLoss := floorLoss)).cellVolumeFloor =
      Kakeya.realRpowENN rho
        (3 / 2 + sigma / 2 + floorLoss + internalLoss / 2) := by
  unfold proposition63_four_call_cell_volume_floor_choice
  dsimp only
  rw [ENNReal.ofReal_toReal]
  · rw [realRpowENN_sqrt rho_pos, realRpowENN_sqrt rho_pos,
      ENNReal.div_eq_inv_mul, realRpowENN_inv rho_pos,
      ← realRpowENN_add rho_pos,
      ← realRpowENN_add rho_pos]
    congr 1
    ring
  · exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
        (by simp [Kakeya.realRpowENN]))
      (by simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos
        (Real.sqrt_pos.2 rho_pos)])

private theorem proposition63_four_call_paper_geometric_exact
    {rho : ℝ} (rho_pos : 0 < rho) :
    4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
        ENNReal.ofReal (4 * rho)) =
      256 * Kakeya.realRpowENN rho 2 := by
  have sqrt_sq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt rho_pos.le
  rw [show 4 * (2 * Real.sqrt rho) ^ 2 = 16 * rho by
    rw [mul_pow, sqrt_sq]; ring]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [ENNReal.ofReal_ofNat, Kakeya.realRpowENN]
  rw [show Real.rpow rho 2 = rho * rho by
    calc
      Real.rpow rho 2 = rho ^ (2 : ℕ) := Real.rpow_natCast rho 2
      _ = rho * rho := pow_two rho]
  rw [ENNReal.ofReal_mul rho_pos.le]
  ring

private theorem proposition63_four_call_exact_ratio_bound
    {rho sigma normalizationLoss internalLoss epsilon₁ angular floorLoss : ℝ}
    {coefficient : NNReal} {cellMass : ENNReal} {coverBudget : ℕ}
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (sigma_le_one : sigma ≤ 1)
    (normalization_nonneg : 0 ≤ normalizationLoss)
    (internal_nonneg : 0 ≤ internalLoss) (epsilon_nonneg : 0 ≤ epsilon₁)
    (angular_nonneg : 0 ≤ angular) (floor_nonneg : 0 ≤ floorLoss)
    (cellMass_pos : 0 < cellMass) (cellMass_finite : cellMass ≠ ⊤)
    (coverBudget_pos : 0 < coverBudget)
    (cell_lower : ENNReal.ofReal
        (proposition63_four_call_cell_volume_floor_choice rho_pos
          (Real.sqrt_pos.2 rho_pos) (sigma := sigma)
          (outputLoss := internalLoss) (floorLoss := floorLoss)).cellVolumeFloor ≤
        cellMass)
    (cover_upper : (coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            internalLoss epsilon₁ angular)) + 2) :
    (((cellMass / 2) / (2 * (coverBudget : ENNReal)))⁻¹ *
        (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
          ENNReal.ofReal (4 * rho)))) ≤
      1024 * ((1605264998400 : ENNReal) *
          (coefficient : ENNReal) ^ 3 + 2) *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperCoarseBurden normalizationLoss
            internalLoss epsilon₁ angular floorLoss)) := by
  let A : ENNReal := (1605264998400 : ENNReal) *
    (coefficient : ENNReal) ^ 3
  let finalExponent : ℝ := proposition63FourCallPaperFinalExponent sigma
    normalizationLoss internalLoss epsilon₁ angular
  let cellExponent : ℝ :=
    3 / 2 + sigma / 2 + floorLoss + internalLoss / 2
  let burden : ℝ := proposition63FourCallPaperCoarseBurden
    normalizationLoss internalLoss epsilon₁ angular floorLoss
  have finalExponent_nonneg : 0 ≤ finalExponent := by
    dsimp only [finalExponent, proposition63FourCallPaperFinalExponent]
    linarith
  have burden_nonneg : 0 ≤ burden := by
    dsimp only [burden, proposition63FourCallPaperCoarseBurden]
    linarith
  have power_ge_one : 1 ≤ Kakeya.realRpowENN rho (-finalExponent) := by
    simpa [Kakeya.realRpowENN] using
      (realRpowENN_antitone rho_pos rho_le_one
        (show -finalExponent ≤ 0 by linarith))
  have cover_monomial : (coverBudget : ENNReal) ≤
      (A + 2) * Kakeya.realRpowENN rho (-finalExponent) := by
    calc
      (coverBudget : ENNReal) ≤
          A * Kakeya.realRpowENN rho (-finalExponent) + 2 := by
        simpa only [A, finalExponent] using cover_upper
      _ ≤ A * Kakeya.realRpowENN rho (-finalExponent) +
          2 * Kakeya.realRpowENN rho (-finalExponent) := by
        have htwo : (2 : ENNReal) ≤
            2 * Kakeya.realRpowENN rho (-finalExponent) := by
          calc
            (2 : ENNReal) = 2 * 1 := by ring
            _ ≤ 2 * Kakeya.realRpowENN rho (-finalExponent) := by gcongr
        exact add_le_add_right htwo _
      _ = (A + 2) * Kakeya.realRpowENN rho (-finalExponent) := by ring
  have cell_exact : ENNReal.ofReal
      (proposition63_four_call_cell_volume_floor_choice rho_pos
        (Real.sqrt_pos.2 rho_pos) (sigma := sigma)
        (outputLoss := internalLoss) (floorLoss := floorLoss)).cellVolumeFloor =
      Kakeya.realRpowENN rho cellExponent := by
    simpa only [cellExponent] using
      proposition63_four_call_cell_floor_exact (rho_pos := rho_pos)
        (sigma := sigma) (internalLoss := internalLoss)
        (floorLoss := floorLoss)
  have exponent_eq : 2 - finalExponent - cellExponent = -burden := by
    dsimp only [finalExponent, cellExponent, burden,
      proposition63FourCallPaperFinalExponent,
      proposition63FourCallPaperCoarseBurden]
    ring
  have left_pos : 0 < (cellMass / 2) / (2 * (coverBudget : ENNReal)) := by
    exact ENNReal.div_pos (ENNReal.div_pos cellMass_pos.ne' (by norm_num)).ne'
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top coverBudget))
  have left_top : (cellMass / 2) / (2 * (coverBudget : ENNReal)) ≠ ⊤ := by
    exact ENNReal.div_ne_top
      (ENNReal.div_ne_top cellMass_finite (by norm_num))
      (by positivity)
  apply (ENNReal.inv_mul_le_iff left_pos.ne' left_top).2
  rw [proposition63_four_call_paper_geometric_exact rho_pos]
  rw [show (cellMass / 2) / (2 * (coverBudget : ENNReal)) *
      (1024 * (A + 2) * Kakeya.realRpowENN rho (-burden)) =
      ((cellMass / 2) * (1024 * (A + 2) *
        Kakeya.realRpowENN rho (-burden))) /
          (2 * (coverBudget : ENNReal)) by
    simp only [ENNReal.div_eq_inv_mul]
    ring]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by positivity : (2 * (coverBudget : ENNReal)) ≠ 0))
    (Or.inl (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.natCast_ne_top coverBudget)))).2
  rw [show (cellMass / 2) *
      (1024 * (A + 2) * Kakeya.realRpowENN rho (-burden)) =
      (cellMass * (1024 * (A + 2) *
        Kakeya.realRpowENN rho (-burden))) / 2 by
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    ring]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (by norm_num : (2 : ENNReal) ≠ 0))
    (Or.inl (by norm_num : (2 : ENNReal) ≠ ⊤))).2
  have power_eq :
      Kakeya.realRpowENN rho 2 *
          Kakeya.realRpowENN rho (-finalExponent) =
        Kakeya.realRpowENN rho cellExponent *
          Kakeya.realRpowENN rho (-burden) := by
    rw [← realRpowENN_add rho_pos, ← realRpowENN_add rho_pos]
    congr 1
    linarith [exponent_eq]
  calc
    (256 * Kakeya.realRpowENN rho 2) *
          (2 * (coverBudget : ENNReal)) * 2 ≤
        (256 * Kakeya.realRpowENN rho 2) *
          (2 * ((A + 2) * Kakeya.realRpowENN rho (-finalExponent))) * 2 := by
      gcongr
    _ = Kakeya.realRpowENN rho cellExponent *
        (1024 * (A + 2) * Kakeya.realRpowENN rho (-burden)) := by
      calc
        _ = 1024 * (A + 2) *
            (Kakeya.realRpowENN rho 2 *
              Kakeya.realRpowENN rho (-finalExponent)) := by ring
        _ = 1024 * (A + 2) *
            (Kakeya.realRpowENN rho cellExponent *
              Kakeya.realRpowENN rho (-burden)) := by rw [power_eq]
        _ = _ := by ring
    _ ≤ cellMass *
        (1024 * (A + 2) * Kakeya.realRpowENN rho (-burden)) := by
      rw [cell_exact] at cell_lower
      gcongr

private theorem proposition63_four_call_exact_massLoss_bound
    {rho sigma normalizationLoss internalLoss epsilon₁ angular floorLoss : ℝ}
    {coefficient : NNReal} {cellMass : ENNReal} {coverBudget : ℕ}
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (sigma_le_one : sigma ≤ 1)
    (normalization_nonneg : 0 ≤ normalizationLoss)
    (internal_nonneg : 0 ≤ internalLoss) (epsilon_nonneg : 0 ≤ epsilon₁)
    (angular_nonneg : 0 ≤ angular) (floor_nonneg : 0 ≤ floorLoss)
    (cellMass_pos : 0 < cellMass) (cellMass_finite : cellMass ≠ ⊤)
    (coverBudget_pos : 0 < coverBudget)
    (cell_lower : ENNReal.ofReal
        (proposition63_four_call_cell_volume_floor_choice rho_pos
          (Real.sqrt_pos.2 rho_pos) (sigma := sigma)
          (outputLoss := internalLoss) (floorLoss := floorLoss)).cellVolumeFloor ≤
        cellMass)
    (cover_upper : (coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperFinalExponent sigma normalizationLoss
            internalLoss epsilon₁ angular)) + 2) :
    proposition63Lemma43MassLoss
        ((cellMass / 2) / (2 * (coverBudget : ENNReal)))
        (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
          ENNReal.ofReal (4 * rho))) ≤
      proposition63FourCallPaperCoarseCoefficient coefficient *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperCoarseBurden normalizationLoss
            internalLoss epsilon₁ angular floorLoss)) := by
  have burden_nonneg : 0 ≤ proposition63FourCallPaperCoarseBurden
      normalizationLoss internalLoss epsilon₁ angular floorLoss := by
    dsimp only [proposition63FourCallPaperCoarseBurden]
    linarith
  have power_ge_one : 1 ≤ Kakeya.realRpowENN rho
      (-(proposition63FourCallPaperCoarseBurden normalizationLoss
        internalLoss epsilon₁ angular floorLoss)) := by
    simpa [Kakeya.realRpowENN] using
      (realRpowENN_antitone rho_pos rho_le_one
        (show -(proposition63FourCallPaperCoarseBurden normalizationLoss
          internalLoss epsilon₁ angular floorLoss) ≤ 0 by linarith))
  unfold proposition63Lemma43MassLoss
  calc
    1 + ((cellMass / 2) / (2 * (coverBudget : ENNReal)))⁻¹ *
          (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
            ENNReal.ofReal (4 * rho))) ≤
        Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperCoarseBurden normalizationLoss
              internalLoss epsilon₁ angular floorLoss)) +
          1024 * ((1605264998400 : ENNReal) *
              (coefficient : ENNReal) ^ 3 + 2) *
            Kakeya.realRpowENN rho
              (-(proposition63FourCallPaperCoarseBurden normalizationLoss
                internalLoss epsilon₁ angular floorLoss)) :=
      add_le_add power_ge_one
        (proposition63_four_call_exact_ratio_bound rho_pos rho_le_one
          sigma_le_one normalization_nonneg internal_nonneg epsilon_nonneg
          angular_nonneg floor_nonneg cellMass_pos cellMass_finite
          coverBudget_pos cell_lower cover_upper)
    _ = proposition63FourCallPaperCoarseCoefficient coefficient *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperCoarseBurden normalizationLoss
            internalLoss epsilon₁ angular floorLoss)) := by
      unfold proposition63FourCallPaperCoarseCoefficient
      ring

/-- A family-free cutoff, chosen before the runtime coarse scale. -/
structure Proposition63FourCallPaperCoarseAbsorptionData
    (coefficient : ENNReal)
    (normalizationLoss internalLoss epsilon₁ angular floorLoss
      candidateLoss finalLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ {rho : ℝ}, 0 < rho → rho ≤ delta₀ →
    ∀ {massLoss : ENNReal},
      massLoss ≤ coefficient * Kakeya.realRpowENN rho
        (-(proposition63FourCallPaperCoarseBurden normalizationLoss
          internalLoss epsilon₁ angular floorLoss)) →
      massLoss * Kakeya.realRpowENN rho candidateLoss ≤
        Kakeya.realRpowENN rho finalLoss

theorem proposition63_four_call_paper_coarse_absorption
    (coefficient : ENNReal) (coefficient_finite : coefficient ≠ ⊤)
    (normalizationLoss internalLoss epsilon₁ angular floorLoss
      candidateLoss finalLoss : ℝ)
    (gap : proposition63FourCallPaperCoarseBurden normalizationLoss
        internalLoss epsilon₁ angular floorLoss < candidateLoss - finalLoss) :
    Nonempty (Proposition63FourCallPaperCoarseAbsorptionData coefficient
      normalizationLoss internalLoss epsilon₁ angular floorLoss
      candidateLoss finalLoss) := by
  let residual : ℝ := candidateLoss - finalLoss -
    proposition63FourCallPaperCoarseBurden normalizationLoss internalLoss
      epsilon₁ angular floorLoss
  have residual_pos : 0 < residual := by
    dsimp only [residual]
    linarith
  rcases exists_delta_realRpowENN_bound coefficient coefficient_finite
      residual_pos with ⟨delta₀, delta₀_pos, delta₀_le_one, bound⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀_pos
    delta₀_le_one := delta₀_le_one
    absorb := ?_
  }⟩
  intro rho rho_pos rho_le massLoss massLoss_le
  have coefficient_le : coefficient ≤ Kakeya.realRpowENN rho (-residual) :=
    bound rho rho_pos rho_le
  calc
    massLoss * Kakeya.realRpowENN rho candidateLoss ≤
        (coefficient * Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperCoarseBurden normalizationLoss
            internalLoss epsilon₁ angular floorLoss))) *
          Kakeya.realRpowENN rho candidateLoss := by gcongr
    _ = coefficient * Kakeya.realRpowENN rho
          (candidateLoss - proposition63FourCallPaperCoarseBurden
            normalizationLoss internalLoss epsilon₁ angular floorLoss) := by
      rw [show Kakeya.realRpowENN rho
          (candidateLoss - proposition63FourCallPaperCoarseBurden
            normalizationLoss internalLoss epsilon₁ angular floorLoss) =
          Kakeya.realRpowENN rho
              (-(proposition63FourCallPaperCoarseBurden normalizationLoss
                internalLoss epsilon₁ angular floorLoss)) *
            Kakeya.realRpowENN rho candidateLoss by
        rw [← realRpowENN_add rho_pos]
        congr 1
        ring]
      ring
    _ ≤ Kakeya.realRpowENN rho (-residual) *
          Kakeya.realRpowENN rho
            (candidateLoss - proposition63FourCallPaperCoarseBurden
              normalizationLoss internalLoss epsilon₁ angular floorLoss) := by
      gcongr
    _ = Kakeya.realRpowENN rho finalLoss := by
      rw [← realRpowENN_add rho_pos]
      congr 1
      dsimp only [residual]
      ring

/-- The same coarse absorption with an externally prescribed cutoff.  This
form is used by the outer power envelope: the endpoint inequality pays the
runtime Lipschitz coefficient at a cutoff chosen before the runtime scale. -/
def proposition63_four_call_paper_coarse_absorption_at
    (coefficient : ENNReal)
    (normalizationLoss internalLoss epsilon₁ angular floorLoss
      candidateLoss finalLoss delta₀ : ℝ)
    (delta₀_pos : 0 < delta₀) (delta₀_le_one : delta₀ ≤ 1)
    (gap : proposition63FourCallPaperCoarseBurden normalizationLoss
        internalLoss epsilon₁ angular floorLoss < candidateLoss - finalLoss)
    (endpoint : coefficient ≤ Kakeya.realRpowENN delta₀
      (-(candidateLoss - finalLoss -
        proposition63FourCallPaperCoarseBurden normalizationLoss internalLoss
          epsilon₁ angular floorLoss))) :
    Proposition63FourCallPaperCoarseAbsorptionData coefficient
      normalizationLoss internalLoss epsilon₁ angular floorLoss
      candidateLoss finalLoss where
  delta₀ := delta₀
  delta₀_pos := delta₀_pos
  delta₀_le_one := delta₀_le_one
  absorb := by
    intro rho rho_pos rho_le massLoss massLoss_le
    let residual := candidateLoss - finalLoss -
      proposition63FourCallPaperCoarseBurden normalizationLoss internalLoss
        epsilon₁ angular floorLoss
    have residual_pos : 0 < residual := by
      dsimp only [residual]
      linarith
    have coefficient_le : coefficient ≤
        Kakeya.realRpowENN rho (-residual) :=
      endpoint.trans <| by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_nonpos rho_pos rho_le (by linarith)
    calc
      massLoss * Kakeya.realRpowENN rho candidateLoss ≤
          (coefficient * Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperCoarseBurden normalizationLoss
              internalLoss epsilon₁ angular floorLoss))) *
            Kakeya.realRpowENN rho candidateLoss := by gcongr
      _ = coefficient * Kakeya.realRpowENN rho
            (candidateLoss - proposition63FourCallPaperCoarseBurden
              normalizationLoss internalLoss epsilon₁ angular floorLoss) := by
        rw [show Kakeya.realRpowENN rho
            (candidateLoss - proposition63FourCallPaperCoarseBurden
              normalizationLoss internalLoss epsilon₁ angular floorLoss) =
            Kakeya.realRpowENN rho
                (-(proposition63FourCallPaperCoarseBurden normalizationLoss
                  internalLoss epsilon₁ angular floorLoss)) *
              Kakeya.realRpowENN rho candidateLoss by
          rw [← realRpowENN_add rho_pos]
          congr 1
          ring]
        ring
      _ ≤ Kakeya.realRpowENN rho (-residual) *
            Kakeya.realRpowENN rho
              (candidateLoss - proposition63FourCallPaperCoarseBurden
                normalizationLoss internalLoss epsilon₁ angular floorLoss) := by
        gcongr
      _ = Kakeya.realRpowENN rho finalLoss := by
        rw [← realRpowENN_add rho_pos]
        congr 1
        dsimp only [residual]
        ring

/-- The staged loss seed supplies the exact strict gap for coarse A. -/
theorem Proposition63FourCallInnerLossSeed.paperCoarseAbsorption
    {sigma outputLoss discreteLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (coefficient : ENNReal) (coefficient_finite : coefficient ≠ ⊤) :
    Nonempty (Proposition63FourCallPaperCoarseAbsorptionData coefficient
      seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
      seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
      seed.paperCandidateLoss seed.finalLoss) := by
  apply proposition63_four_call_paper_coarse_absorption coefficient
    coefficient_finite
  dsimp only [proposition63FourCallPaperCoarseBurden]
  linarith [seed.paperCoarseBurden_lt_candidate]

namespace Proposition63NestedPointCoverData.FullGrainCells

/-- Exact coarse-A restoration of the paper candidate. -/
theorem prepared_paperCandidate_coarse_restore_of_exact_choices
    {sigma outputLoss discreteLoss rho inputLoss initialNormalizationLoss
      firstLoss reentryLoss
      secondLoss tauScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss rho}
    {normalizationExponent : ℕ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialNormalizationLoss) source
      normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {coefficient : NNReal}
    (coverBudget : ℕ)
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := seed.fourthKernel.internalLoss)
      (secondLoss := secondLoss) (finalLoss := seed.finalLoss)
      (queryScale := rho) (tauScale := tauScale)
      (sqrtScale := Real.sqrt rho) initialNormalized planeMap tauConstant
      sqrtConstant)
    {lineVolume : ℝ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (absorption : Proposition63FourCallPaperCoarseAbsorptionData
      (proposition63FourCallPaperCoarseCoefficient coefficient)
      seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
      seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
      seed.paperCandidateLoss seed.finalLoss)
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (rho_le_absorption : rho ≤ absorption.delta₀)
    (critical : PureWZ2CriticalFloorSelectionData
      sigma seed.floorLoss seed.structuralBudget)
    (rho_le_critical : rho ≤ critical.delta₀)
    (final_le_structural : seed.finalLoss ≤ critical.structuralLoss)
    (traceAbsorption : Proposition63PureCriticalTailTraceAbsorption rho
      critical.structuralLoss reentryLoss seed.finalLoss)
    (floor_nonneg : 0 ≤ seed.floorLoss)
    (coverBudget_pos : 0 < coverBudget)
    (cover_upper : (coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperFinalExponent sigma
            seed.schedule.fourth.normalizationLoss
            seed.fourthKernel.internalLoss seed.epsilon₁
            seed.paperAngularExponent)) + 2)
    (candidate_pos : 0 < seed.paperCandidateLoss)
    {constant : ENNReal}
    (covering : PureWZ2IntervalCoveringAt (full.paperCandidate rho_pos)
      planeMap rho (Real.toNNReal rho) (Real.toNNReal tauScale) constant) :
    ∃ restored : PureWZ2IntervalLocalGrainData
        (sigma := sigma) (outputLoss := seed.paperCandidateLoss)
        (source := data.prepared.refined.shading) planeMap rho
        (Real.toNNReal rho) (Real.toNNReal tauScale) constant,
      restored.shading = full.paperCandidate rho_pos := by
  let cellChoice := proposition63_four_call_cell_volume_floor_choice rho_pos
    (Real.sqrt_pos.2 rho_pos) (sigma := sigma)
    (outputLoss := seed.fourthKernel.internalLoss)
    (floorLoss := seed.floorLoss)
  have cell_lower : ENNReal.ofReal cellChoice.cellVolumeFloor ≤
      data.cells.cellMass := by
    exact data.critical_cellMass_lower_of_pure_critical_trace critical
      rho_le_critical final_le_structural traceAbsorption
      cellChoice.positive.le cellChoice.budget
  have massLoss_bound :
      proposition63Lemma43MassLoss
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))
          (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
            ENNReal.ofReal (4 * rho))) ≤
        proposition63FourCallPaperCoarseCoefficient coefficient *
          Kakeya.realRpowENN rho
            (-(proposition63FourCallPaperCoarseBurden
              seed.schedule.fourth.normalizationLoss
              seed.fourthKernel.internalLoss seed.epsilon₁
              seed.paperAngularExponent seed.floorLoss)) := by
    apply proposition63_four_call_exact_massLoss_bound rho_pos rho_le_one
      seed.sigma_lt_one.le seed.schedule.fourth.normalizationLoss_pos.le
      seed.fourthKernel.internalLoss_pos.le seed.epsilon₁_pos.le
      seed.paperAngularExponent_pos.le floor_nonneg
      data.cells.cellMass_pos data.cells.cellMass_ne_top coverBudget_pos
    · simpa only [cellChoice] using cell_lower
    · exact cover_upper
  have restore_power :
      proposition63Lemma43MassLoss
          ((data.cells.cellMass / 2) /
            (2 * (coverBudget : ENNReal)))
          (4 * (ENNReal.ofReal (4 * (2 * Real.sqrt rho) ^ 2) *
            ENNReal.ofReal (4 * rho))) *
        Kakeya.realRpowENN rho seed.paperCandidateLoss ≤
          Kakeya.realRpowENN rho seed.finalLoss :=
    absorption.absorb rho_pos rho_le_absorption massLoss_bound
  apply full.prepared_paperCandidate_intervalLocalGrain rho_pos rho_pos
    coverBudget_pos covering
  · rw [seed.paperCandidateLoss_eq]
    have output_pos : 0 < outputLoss := by
      rw [seed.paperCandidateLoss_eq] at candidate_pos
      linarith
    linarith [seed.paperCandidateGap]
  · exact candidate_pos
  · exact restore_power

/-- The extremality projection of exact coarse-A restoration.  Keeping this
projection in the small coarse module avoids unfolding the full dependent
local-grain witness inside the ordered-pair consumer. -/
theorem paperCandidate_extremal_of_exact_choices
    {sigma outputLoss discreteLoss rho inputLoss initialNormalizationLoss
      firstLoss reentryLoss
      secondLoss tauScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss rho}
    {normalizationExponent : ℕ}
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialNormalizationLoss) source
      normalizationExponent}
    {planeMap : Point3 → Point3} {tauConstant sqrtConstant : ENNReal}
    {coefficient : NNReal}
    (coverBudget : ℕ)
    (data : Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := seed.fourthKernel.internalLoss)
      (secondLoss := secondLoss) (finalLoss := seed.finalLoss)
      (queryScale := rho) (tauScale := tauScale)
      (sqrtScale := Real.sqrt rho) initialNormalized planeMap tauConstant
      sqrtConstant)
    {lineVolume : ℝ}
    (full : data.FullGrainCells lineVolume coverBudget)
    (absorption : Proposition63FourCallPaperCoarseAbsorptionData
      (proposition63FourCallPaperCoarseCoefficient coefficient)
      seed.schedule.fourth.normalizationLoss seed.fourthKernel.internalLoss
      seed.epsilon₁ seed.paperAngularExponent seed.floorLoss
      seed.paperCandidateLoss seed.finalLoss)
    (rho_pos : 0 < rho) (rho_le_one : rho ≤ 1)
    (rho_le_absorption : rho ≤ absorption.delta₀)
    (critical : PureWZ2CriticalFloorSelectionData
      sigma seed.floorLoss seed.structuralBudget)
    (rho_le_critical : rho ≤ critical.delta₀)
    (final_le_structural : seed.finalLoss ≤ critical.structuralLoss)
    (traceAbsorption : Proposition63PureCriticalTailTraceAbsorption rho
      critical.structuralLoss reentryLoss seed.finalLoss)
    (floor_nonneg : 0 ≤ seed.floorLoss)
    (coverBudget_pos : 0 < coverBudget)
    (cover_upper : (coverBudget : ENNReal) ≤
      (1605264998400 : ENNReal) * (coefficient : ENNReal) ^ 3 *
        Kakeya.realRpowENN rho
          (-(proposition63FourCallPaperFinalExponent sigma
            seed.schedule.fourth.normalizationLoss
            seed.fourthKernel.internalLoss seed.epsilon₁
            seed.paperAngularExponent)) + 2)
    (candidate_pos : 0 < seed.paperCandidateLoss)
    {constant : ENNReal}
    (covering : PureWZ2IntervalCoveringAt (full.paperCandidate rho_pos)
      planeMap rho (Real.toNNReal rho) (Real.toNNReal tauScale) constant) :
    WZ2PaperCroppedIsExtremal sigma seed.paperCandidateLoss
      data.reentry.normalization.croppedFamily
      (full.paperCandidate rho_pos) := by
  rcases full.prepared_paperCandidate_coarse_restore_of_exact_choices
      seed coverBudget data absorption rho_pos rho_le_one
      rho_le_absorption critical rho_le_critical final_le_structural
      traceAbsorption floor_nonneg coverBudget_pos cover_upper candidate_pos
      covering with
    ⟨restored, hrestored⟩
  simpa only [hrestored] using restored.extremal

end Proposition63NestedPointCoverData.FullGrainCells

end Kakeya.Assouad.PureWZ2
