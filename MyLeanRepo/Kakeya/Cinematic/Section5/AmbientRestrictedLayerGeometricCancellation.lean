import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLayerGeometricCancellationInputs

/-!
# Geometric cancellation in the selected-layer local coefficient

This is the pure real-power cancellation needed after the Lambda-aware
fixed-bin volume assembly.

Raise both sides to the eighth power to eliminate all fractional exponents.
The ambient-cardinality, parent-area, and fine-area estimates then cancel the
representative `tRep` and `DeltaRep` scales exactly, leaving one factor of
`delta`.
-/

namespace Kakeya.Cinematic

theorem ambient_restricted_layer_geometric_cancellation :
    AmbientRestrictedLayerGeometricCancellationStatement := by
  intro delta tRep DeltaRep C_R C_shading C_KT parentConstant parentArea cardUpper
    hdelta htRep hDeltaRep hCR hCshading hCKT hparentConstant hparentArea_nonneg hcardUpper_nonneg
    hparentArea hcardUpper
  set fineArea := ambientRestrictedSelectedFineGeometricArea C_shading delta C_R tRep DeltaRep
    with hfineArea_def
  set K := 2 * C_shading * Real.sqrt C_shading with hK_def

  have hK_pos : 0 < K := by positivity
  have hK_nonneg : 0 ≤ K := by linarith
  have h_fineArea_pos : 0 < fineArea := by
    simp only [hfineArea_def, ambientRestrictedSelectedFineGeometricArea]
    positivity
  have h_fineArea_nonneg : 0 ≤ fineArea := by linarith

  have h1 : fineArea = K * delta^2 / Real.sqrt (C_R * tRep * DeltaRep) := by
    simp only [hfineArea_def, ambientRestrictedSelectedFineGeometricArea, hK_def]
    have h_div : (C_shading * delta) / (C_R * tRep * DeltaRep / delta) =
        C_shading * delta^2 / (C_R * tRep * DeltaRep) := by
      field_simp [hdelta.ne', hCR.ne', htRep.ne', hDeltaRep.ne']
    rw [h_div]
    have h_sqrt2 : Real.sqrt (C_shading * delta^2 / (C_R * tRep * DeltaRep)) =
        Real.sqrt C_shading * delta / Real.sqrt (C_R * tRep * DeltaRep) := by
      rw [Real.sqrt_div (by positivity)]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (show 0 ≤ delta by linarith)]
    rw [h_sqrt2] <;> ring

  have h_cardUpper' : cardUpper ≤ 3 * C_KT * tRep / delta := by
    have h : C_KT * 3 * tRep / delta = 3 * C_KT * tRep / delta := by ring
    rw [h] at hcardUpper
    exact hcardUpper
  have h2 : cardUpper^4 ≤ (3 * C_KT)^4 * tRep^4 / delta^4 := by
    calc
      cardUpper^4 ≤ (3 * C_KT * tRep / delta)^4 := by gcongr
      _ = (3 * C_KT)^4 * tRep^4 / delta^4 := by
        field_simp [hdelta.ne']

  have h3 : parentArea^2 ≤ parentConstant^2 * DeltaRep^3 / (C_R * tRep) := by
    calc
      parentArea^2 ≤ (parentConstant * DeltaRep * Real.sqrt (DeltaRep / (C_R * tRep)))^2 := by
        gcongr
      _ = parentConstant^2 * DeltaRep^2 * (Real.sqrt (DeltaRep / (C_R * tRep)))^2 := by ring
      _ = parentConstant^2 * DeltaRep^2 * (DeltaRep / (C_R * tRep)) := by
        rw [Real.sq_sqrt] <;> positivity
      _ = parentConstant^2 * DeltaRep^3 / (C_R * tRep) := by
        field_simp [hCR.ne', htRep.ne']

  set S := Real.sqrt (C_R * tRep * DeltaRep) with hS_def
  have hS_pos : 0 < S := by positivity
  have hS_sq : S^2 = C_R * tRep * DeltaRep := by
    simp only [hS_def]
    rw [Real.sq_sqrt] <;> positivity

  have h4 : fineArea^6 = K^6 * delta^12 / (C_R * tRep * DeltaRep)^3 := by
    rw [h1]
    have h : (K * delta^2 / S)^6 = K^6 * delta^12 / S^6 := by
      field_simp [hS_pos.ne']
    rw [h]
    have hS6 : S^6 = (C_R * tRep * DeltaRep)^3 := by
      have h : S^6 = (S^2)^3 := by ring
      rw [h, hS_sq]
    rw [hS6]

  have h_sqrt3CKT_8 : (Real.sqrt (3 * C_KT))^8 = (3 * C_KT)^4 := by
    have h_pos : 0 ≤ 3 * C_KT := by positivity
    have h : (Real.sqrt (3 * C_KT))^2 = 3 * C_KT := Real.sq_sqrt h_pos
    have h2 : (Real.sqrt (3 * C_KT))^8 = ((Real.sqrt (3 * C_KT))^2)^4 := by ring
    rw [h2, h] <;> ring

  have h_pc_8 : (Real.rpow parentConstant (1 / 4 : ℝ))^8 = parentConstant^2 := by
    have h_eq : Real.rpow parentConstant ((1 / 4 : ℝ) * (8 : ℕ)) =
        (Real.rpow parentConstant (1 / 4 : ℝ))^8 :=
      Real.rpow_mul_natCast (by positivity) (1 / 4 : ℝ) 8
    have h2 : (1 / 4 : ℝ) * (8 : ℕ) = (2 : ℝ) := by norm_num
    rw [h2] at h_eq
    simpa using h_eq.symm

  have h_K_8 : (Real.rpow K (3 / 4 : ℝ))^8 = K^6 := by
    have h_eq : Real.rpow K ((3 / 4 : ℝ) * (8 : ℕ)) =
        (Real.rpow K (3 / 4 : ℝ))^8 :=
      Real.rpow_mul_natCast hK_nonneg (3 / 4 : ℝ) 8
    have h2 : (3 / 4 : ℝ) * (8 : ℕ) = (6 : ℝ) := by norm_num
    rw [h2] at h_eq
    simpa using h_eq.symm

  have h_sqrtCR_8 : (Real.sqrt C_R)^8 = C_R^4 := by
    have h_pos : 0 ≤ C_R := by linarith
    have h : (Real.sqrt C_R)^2 = C_R := Real.sq_sqrt h_pos
    have h2 : (Real.sqrt C_R)^8 = ((Real.sqrt C_R)^2)^4 := by ring
    rw [h2, h] <;> ring

  set C := Real.sqrt (3 * C_KT) * Real.rpow parentConstant (1 / 4 : ℝ) *
      Real.rpow K (3 / 4 : ℝ) / Real.sqrt C_R with hC_def

  have hC_nonneg : 0 ≤ C := by
    simp only [hC_def]
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · exact Real.sqrt_nonneg _
        · exact Real.rpow_nonneg (by linarith) _
      · exact Real.rpow_nonneg hK_nonneg _
    · exact Real.sqrt_nonneg _
  have hCR_ne_zero : C_R ≠ 0 := hCR.ne'
  have h_sqrtCR_ne_zero : Real.sqrt C_R ≠ 0 := by positivity

  have hC8 : C^8 = (3 * C_KT)^4 * parentConstant^2 * K^6 / C_R^4 := by
    simp only [hC_def]
    have h_expand : (Real.sqrt (3 * C_KT) * Real.rpow parentConstant (1 / 4 : ℝ) * Real.rpow K (3 / 4 : ℝ) / Real.sqrt C_R)^8 =
        (Real.sqrt (3 * C_KT))^8 * (Real.rpow parentConstant (1 / 4 : ℝ))^8 * (Real.rpow K (3 / 4 : ℝ))^8 / (Real.sqrt C_R)^8 := by
      field_simp [h_sqrtCR_ne_zero] <;> ring
    rw [h_expand]
    rw [h_sqrt3CKT_8, h_pc_8, h_K_8, h_sqrtCR_8]
    <;> field_simp [hCR_ne_zero] <;> ring

  set LHS := Real.sqrt cardUpper * Real.rpow parentArea (1 / 4 : ℝ) * Real.rpow fineArea (3 / 4 : ℝ)
    with hLHS_def
  set RHS := C * delta with hRHS_def

  have hLHS_nonneg : 0 ≤ LHS := by
    simp only [hLHS_def]
    apply mul_nonneg
    · apply mul_nonneg
      · exact Real.sqrt_nonneg _
      · exact Real.rpow_nonneg hparentArea_nonneg _
    · exact Real.rpow_nonneg h_fineArea_nonneg _
  have hRHS_nonneg : 0 ≤ RHS := by positivity

  have h_sqrt_card_8 : (Real.sqrt cardUpper)^8 = cardUpper^4 := by
    have h : (Real.sqrt cardUpper)^2 = cardUpper := Real.sq_sqrt hcardUpper_nonneg
    have h2 : (Real.sqrt cardUpper)^8 = ((Real.sqrt cardUpper)^2)^4 := by ring
    rw [h2, h] <;> ring

  have h_parent_8 : (Real.rpow parentArea (1 / 4 : ℝ))^8 = parentArea^2 := by
    have h_eq : Real.rpow parentArea ((1 / 4 : ℝ) * (8 : ℕ)) =
        (Real.rpow parentArea (1 / 4 : ℝ))^8 :=
      Real.rpow_mul_natCast hparentArea_nonneg (1 / 4 : ℝ) 8
    have h2 : (1 / 4 : ℝ) * (8 : ℕ) = (2 : ℝ) := by norm_num
    rw [h2] at h_eq
    simpa using h_eq.symm

  have h_fine_8 : (Real.rpow fineArea (3 / 4 : ℝ))^8 = fineArea^6 := by
    have h_eq : Real.rpow fineArea ((3 / 4 : ℝ) * (8 : ℕ)) =
        (Real.rpow fineArea (3 / 4 : ℝ))^8 :=
      Real.rpow_mul_natCast h_fineArea_nonneg (3 / 4 : ℝ) 8
    have h2 : (3 / 4 : ℝ) * (8 : ℕ) = (6 : ℝ) := by norm_num
    rw [h2] at h_eq
    simpa using h_eq.symm

  have hLHS8 : LHS^8 = cardUpper^4 * parentArea^2 * fineArea^6 := by
    simp only [hLHS_def]
    have h_expand : (Real.sqrt cardUpper * Real.rpow parentArea (1 / 4 : ℝ) * Real.rpow fineArea (3 / 4 : ℝ))^8 =
        (Real.sqrt cardUpper)^8 * (Real.rpow parentArea (1 / 4 : ℝ))^8 * (Real.rpow fineArea (3 / 4 : ℝ))^8 := by ring
    rw [h_expand, h_sqrt_card_8, h_parent_8, h_fine_8] <;> ring

  have hRHS8 : RHS^8 = C^8 * delta^8 := by
    simp only [hRHS_def] <;> ring

  have h_main : cardUpper^4 * parentArea^2 * fineArea^6 ≤ C^8 * delta^8 := by
    rw [h4, hC8]
    calc
      cardUpper^4 * parentArea^2 * (K^6 * delta^12 / (C_R * tRep * DeltaRep)^3)
        ≤ ((3 * C_KT)^4 * tRep^4 / delta^4) *
            (parentConstant^2 * DeltaRep^3 / (C_R * tRep)) *
            (K^6 * delta^12 / (C_R * tRep * DeltaRep)^3) := by
          gcongr <;> positivity
      _ = (3 * C_KT)^4 * parentConstant^2 * K^6 / C_R^4 * delta^8 := by
          field_simp [hdelta.ne', hCR.ne', htRep.ne', hDeltaRep.ne'] <;> ring

  have hLHS8_le_RHS8 : LHS^8 ≤ RHS^8 := by
    rw [hLHS8, hRHS8]
    exact h_main

  have h_final : LHS ≤ RHS := by
    by_contra h
    have h' : RHS < LHS := by linarith
    have h'' : RHS^8 < LHS^8 := by
      gcongr <;> linarith
    linarith

  simpa [hLHS_def, hRHS_def, hC_def, hK_def] using h_final

end Kakeya.Cinematic
