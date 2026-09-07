import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.WolffVolumeFloorFromAssertionDRefinement
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
Convert the expanded small-scale shaded hairbrush estimate to the exact
`Kakeya.AssertionD (1 / 2) 0` normalization, including empty families, large
scales, tube-volume normalization, and fixed-constant absorption.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The mass of a tube family equals `enncard * deltaTubeVolume`. -/
lemma helper_mass_eq {δ : ℝ} (F : Kakeya.TubeFamily δ) :
    F.mass = F.enncard * Kakeya.deltaTubeVolume δ := by
  have hvol : ∀ T ∈ F, T.volume = Kakeya.deltaTubeVolume δ :=
    fun T _ => tube_volume_scaling.1 δ T
  calc
    F.mass = ∑ T ∈ F, T.volume := by rfl
    _ = ∑ T ∈ F, Kakeya.deltaTubeVolume δ := by
      apply Finset.sum_congr rfl
      intro T hT
      exact hvol T hT
    _ = (F.card : ENNReal) * Kakeya.deltaTubeVolume δ := by
      simp [Finset.sum_const]
    _ = F.enncard * Kakeya.deltaTubeVolume δ := by
      simp [Kakeya.TubeFamily.enncard]

/-- Monotonicity of `realRpowENN` for nonnegative exponent. -/
lemma helper_realRpowENN_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    {e : ℝ} (he : 0 ≤ e) :
    Kakeya.realRpowENN x e ≤ Kakeya.realRpowENN y e := by
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono (Real.rpow_le_rpow hx.le hxy he)

/-- Antitonicity of `realRpowENN` for nonpositive exponent. -/
lemma helper_realRpowENN_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    {e : ℝ} (he : e ≤ 0) :
    Kakeya.realRpowENN y e ≤ Kakeya.realRpowENN x e := by
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_mono (Real.rpow_le_rpow_of_nonpos hx hxy he)

/-- No δ-tube is contained in the unit ball when δ > 1/2. -/
lemma helper_no_tube_large_delta {δ : ℝ} (hδ : 1 / 2 < δ)
    (T : Kakeya.DeltaTube δ) : ¬ T.IsInUnitBall := by
  intro hT
  have hδ_pos : 0 < δ := by linarith
  let x := T.base - δ • T.direction
  let y := T.base + (1 + δ) • T.direction
  have hdir : ‖T.direction‖ = 1 := T.direction_unit
  have hbase : T.base ∈ Kakeya.unitSegment T.base T.direction :=
    ⟨0, by norm_num, by simp⟩
  have hend : T.base + T.direction ∈ Kakeya.unitSegment T.base T.direction :=
    ⟨1, by norm_num, by simp⟩
  have hnorm_smul : ∀ (c : ℝ), ‖c • T.direction‖ = |c| := by
    intro c
    calc
      ‖c • T.direction‖ = ‖c‖ * ‖T.direction‖ := norm_smul c T.direction
      _ = ‖c‖ * 1 := by rw [hdir]
      _ = ‖c‖ := by ring
      _ = |c| := by simp
  have hdx_base : dist x T.base = δ := by
    have h : x - T.base = (-δ) • T.direction := by simp [x]
    rw [dist_eq_norm, h, hnorm_smul (-δ), abs_neg, abs_of_pos hδ_pos]
  have hdy_end : dist y (T.base + T.direction) = δ := by
    have h : y - (T.base + T.direction) = δ • T.direction := by
      dsimp only [y]
      have h1 : (T.base + (1 + δ) • T.direction) - (T.base + T.direction)
          = (1 + δ) • T.direction - T.direction := by abel
      rw [h1]
      have h2 : (1 + δ) • T.direction - T.direction = δ • T.direction := by
        have h4 : (1 + δ) • T.direction = (1 : ℝ) • T.direction + δ • T.direction := by
          rw [add_smul (1 : ℝ) δ T.direction]
        rw [h4]
        simp
      exact h2
    rw [dist_eq_norm, h, hnorm_smul δ, abs_of_pos hδ_pos]
  have hx_in : x ∈ T.carrier := by
    exact Metric.mem_cthickening_of_dist_le x T.base δ
      (Kakeya.unitSegment T.base T.direction) hbase (by linarith)
  have hy_in : y ∈ T.carrier := by
    exact Metric.mem_cthickening_of_dist_le y (T.base + T.direction) δ
      (Kakeya.unitSegment T.base T.direction) hend (by linarith)
  have hx_ball : x ∈ Kakeya.DeltaTube.unitBall := hT hx_in
  have hy_ball : y ∈ Kakeya.DeltaTube.unitBall := hT hy_in
  have hdx0 : dist x 0 ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hx_ball
  have hdy0 : dist y 0 ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hy_ball
  have hdist : dist x y ≤ 2 := by
    calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
         _ = dist x 0 + dist y 0 := by rw [dist_comm 0 y]
         _ ≤ 1 + 1 := by linarith
         _ = 2 := by norm_num
  have hdist2 : dist x y = 1 + 2 * δ := by
    have h : y - x = (1 + 2 * δ) • T.direction := by
      dsimp only [y, x]
      have h1 : (T.base + (1 + δ) • T.direction) - (T.base - δ • T.direction)
          = (1 + δ) • T.direction + δ • T.direction := by abel
      rw [h1]
      rw [← add_smul (1 + δ) δ T.direction]
      have h2 : (1 + δ) + δ = 1 + 2 * δ := by ring
      rw [h2]
    have h2 : dist x y = dist y x := dist_comm x y
    rw [h2, dist_eq_norm, h, hnorm_smul (1 + 2 * δ)]
    have hpos : 0 ≤ 1 + 2 * δ := by linarith
    rw [abs_of_nonneg hpos]
  rw [hdist2] at hdist
  linarith

theorem proposition1_8_assembly : Proposition1_8AssemblyStatement := by
  intro h
  have h_assertionD : Kakeya.AssertionD (1 / 2) 0 := by
    refine ⟨by norm_num, by norm_num, fun ε hε => ?_⟩
    rcases h ε hε with ⟨κ_h, η_h, δ₀, hκ_h, hη_h, hδ₀, hδ₀1, h_hairbrush⟩
    let η' := η_h
    let V₁ : ENNReal := Kakeya.deltaTubeVolume 1
    have hV1_pos : 0 < V₁ := (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).1
    have hV1_top : V₁ ≠ ⊤ := (tube_volume_scaling.2.1 1 (by norm_num) (by norm_num)).2
    let Cvol : ENNReal := 24 * V₁
    have hCvol_pos : 0 < Cvol := by
      dsimp only [Cvol]
      have h1 : (24 : ENNReal) ≠ 0 := by norm_num
      have h2 : V₁ ≠ 0 := hV1_pos.ne'
      exact bot_lt_iff_ne_bot.mpr (mul_ne_zero h1 h2)
    have hCvol_top : Cvol ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hV1_top
    let Cvol_pow : ENNReal := ENNReal.rpow Cvol (3 / 4)
    have hCvol_pow_pos : 0 < Cvol_pow :=
      ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hCvol_pos.ne') hCvol_top
    have hCvol_pow_top : Cvol_pow ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCvol_top
    let cvol_real : ℝ := Cvol.toReal
    have hcvol_real_pos : 0 < cvol_real := ENNReal.toReal_pos hCvol_pos.ne' hCvol_top
    have hCvol_eq : Cvol = ENNReal.ofReal cvol_real := by
      rw [ENNReal.ofReal_toReal hCvol_top]
    have hCvol_pow_eq : Cvol_pow = ENNReal.ofReal (Real.rpow cvol_real (3 / 4)) := by
      dsimp only [Cvol_pow]
      rw [hCvol_eq]
      exact ENNReal.ofReal_rpow_of_nonneg hcvol_real_pos.le (by norm_num)
    let B : ENNReal := MeasureTheory.volume Kakeya.DeltaTube.unitBall
    have hB_pos : 0 < B := by
      dsimp only [B, Kakeya.DeltaTube.unitBall]
      rw [EuclideanSpace.volume_closedBall_fin_three]
      have hpi_pos : 0 < Real.pi := Real.pi_pos
      positivity
    have hB_top : B ≠ ⊤ := by
      dsimp only [B, Kakeya.DeltaTube.unitBall]
      rw [EuclideanSpace.volume_closedBall_fin_three]
      apply ENNReal.mul_ne_top
      · simp
      · exact ENNReal.ofReal_ne_top
    let Bsqrt : ENNReal := ENNReal.rpow B (1 / 2)
    have hBsqrt_pos : 0 < Bsqrt :=
      ENNReal.rpow_pos (bot_lt_iff_ne_bot.mpr hB_pos.ne') hB_top
    have hBsqrt_top : Bsqrt ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hB_top
    have hBsqrt0 : Bsqrt ≠ 0 := hBsqrt_pos.ne'
    let β : ℝ := 3 * η' / 2 - ε + 3 / 2
    let C : ENNReal :=
      if β ≥ 0 then Kakeya.realRpowENN δ₀ β else Kakeya.realRpowENN (1 / 2) β
    have hC_pos : 0 < C := by
      simp [C, Kakeya.realRpowENN] <;> positivity
    have hC_top : C ≠ ⊤ := by
      dsimp only [C]
      split_ifs <;> simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    let C4 : ENNReal := C * Bsqrt⁻¹
    have hC4_top : C4 ≠ ⊤ := ENNReal.mul_ne_top hC_top (ENNReal.inv_ne_top.mpr hBsqrt0)
    have hBsqrt_inv_pos : 0 < Bsqrt⁻¹ := by
      have h : Bsqrt⁻¹ ≠ 0 := by
        intro h2
        rw [ENNReal.inv_eq_zero] at h2
        exact hBsqrt_top h2
      exact bot_lt_iff_ne_bot.mpr h
    have hC4_pos : 0 < C4 := by
      dsimp only [C4]
      exact bot_lt_iff_ne_bot.mpr (mul_ne_zero hC_pos.ne' hBsqrt_inv_pos.ne')
    let κ'_small : ℝ := κ_h / Real.rpow cvol_real (3 / 4)
    let κ'_large : ℝ := C4.toReal
    let κ' : ℝ := min κ'_small κ'_large
    have h_rpow_pos : 0 < Real.rpow cvol_real (3 / 4) :=
      Real.rpow_pos_of_pos hcvol_real_pos (3 / 4)
    have hκ_small_pos : 0 < κ'_small := by
      dsimp only [κ'_small]
      exact div_pos hκ_h h_rpow_pos
    have hκ_large_pos : 0 < κ'_large := by
      dsimp only [κ'_large]
      exact ENNReal.toReal_pos hC4_pos.ne' hC4_top
    have hκ'_pos : 0 < κ' := by
      dsimp only [κ']
      exact lt_min hκ_small_pos hκ_large_pos
    have h_case3 : ENNReal.ofReal κ' * Cvol_pow ≤ ENNReal.ofReal κ_h := by
      have h1 : κ' ≤ κ'_small := min_le_left _ _
      have h2 : ENNReal.ofReal κ' ≤ ENNReal.ofReal κ'_small := ENNReal.ofReal_mono h1
      have h3 : ENNReal.ofReal κ'_small * Cvol_pow = ENNReal.ofReal κ_h := by
        rw [hCvol_pow_eq]
        have h4 : ENNReal.ofReal κ'_small * ENNReal.ofReal (Real.rpow cvol_real (3 / 4)) =
            ENNReal.ofReal (κ'_small * Real.rpow cvol_real (3 / 4)) := by
          rw [← ENNReal.ofReal_mul hκ_small_pos.le]
        rw [h4]
        dsimp only [κ'_small]
        have h5 : (κ_h / Real.rpow cvol_real (3 / 4)) * Real.rpow cvol_real (3 / 4) = κ_h := by
          field_simp [h_rpow_pos.ne']
        rw [h5]
      calc
        ENNReal.ofReal κ' * Cvol_pow ≤ ENNReal.ofReal κ'_small * Cvol_pow := by gcongr
        _ = ENNReal.ofReal κ_h := h3
    have hC4_eq : ENNReal.ofReal κ'_large = C4 := by
      dsimp only [κ'_large]
      rw [ENNReal.ofReal_toReal hC4_top]
    have h_case4 : ENNReal.ofReal κ' * Bsqrt ≤ C := by
      have h1 : κ' ≤ κ'_large := min_le_right _ _
      have h2 : ENNReal.ofReal κ' ≤ ENNReal.ofReal κ'_large := ENNReal.ofReal_mono h1
      have h3 : ENNReal.ofReal κ'_large * Bsqrt = C := by
        rw [hC4_eq]
        dsimp only [C4]
        rw [mul_assoc]
        have h4 : Bsqrt⁻¹ * Bsqrt = 1 := ENNReal.inv_mul_cancel hBsqrt0 hBsqrt_top
        rw [h4, mul_one]
      calc
        ENNReal.ofReal κ' * Bsqrt ≤ ENNReal.ofReal κ'_large * Bsqrt := by gcongr
        _ = C := h3
    refine ⟨κ', η', hκ'_pos, hη_h, fun δ hδ F hFBall hFDistinct Y hYDense hKT hFrost => ?_⟩
    by_cases hF_empty : F = ∅
    · -- Case 1: F empty
      simp only [Kakeya.AssertionDLowerBound, hF_empty, Kakeya.TubeFamily.enncard,
        Finset.card_empty, Nat.cast_zero]
      <;> simp
    · -- F nonempty
      have hF_nonempty : F.Nonempty := by
        simpa [Finset.nonempty_iff_ne_empty] using hF_empty
      by_cases hδ_large : 1 / 2 < δ
      · -- Case 2: δ > 1/2 implies F empty
        exfalso
        rcases hF_nonempty with ⟨T, hT⟩
        have hT_ball : T.IsInUnitBall := hFBall hT
        exact helper_no_tube_large_delta hδ_large T hT_ball
      · -- δ ≤ 1/2
        have hδ_le_half : δ ≤ 1 / 2 := by linarith
        have hδ1 : δ ≤ 1 := by linarith
        let N := F.enncard
        let V := Kakeya.deltaTubeVolume δ
        have hN_pos : 0 < N := by
          simp [N, Kakeya.TubeFamily.enncard, hF_nonempty]
        have hN0 : N ≠ 0 := hN_pos.ne'
        have hN_top : N ≠ ⊤ := by
          dsimp only [N, Kakeya.TubeFamily.enncard]
          exact ENNReal.natCast_ne_top F.card
        have hV_pos : 0 < V := (tube_volume_scaling.2.1 δ hδ hδ1).1
        have hV0 : V ≠ 0 := hV_pos.ne'
        have hV_top : V ≠ ⊤ := (tube_volume_scaling.2.1 δ hδ hδ1).2
        have h_mass : F.mass = N * V := helper_mass_eq F
        let T_arbitrary : Kakeya.DeltaTube δ :=
          ⟨0, EuclideanSpace.single (0 : Fin 3) 1, by simp⟩
        by_cases hδ_small : δ ≤ δ₀
        · -- Case 3: δ ≤ δ₀ (small scale, apply hairbrush)
          have h_hb := h_hairbrush δ hδ hδ_small F hFBall hFDistinct Y hYDense hKT hFrost
          have h_norm := assertionD_normalization_eq_wolff F.enncard (deltaTubeVolume δ) hN0 hN_top hV0 hV_top
          have hV_upper : V ≤ Cvol * Kakeya.realRpowENN δ 2 := by
            have h2 := tube_volume_scaling.2.2 δ hδ hδ1 T_arbitrary
            have h3 : T_arbitrary.volume = V := tube_volume_scaling.1 δ T_arbitrary
            rw [h3] at h2
            have h4 : V ≤ 24 * Kakeya.realRpowENN δ 2 * V₁ := h2
            have h5 : 24 * Kakeya.realRpowENN δ 2 * V₁ = Cvol * Kakeya.realRpowENN δ 2 := by
              dsimp only [Cvol] <;> ring
            rw [h5] at h4
            exact h4
          have hV_rpow : ENNReal.rpow V (3 / 4) ≤ Cvol_pow * Kakeya.realRpowENN δ (3 / 2) := by
            have h1 : ENNReal.rpow V (3 / 4) ≤ ENNReal.rpow (Cvol * Kakeya.realRpowENN δ 2) (3 / 4) :=
              ENNReal.rpow_le_rpow hV_upper (by norm_num)
            have h2 : ENNReal.rpow (Cvol * Kakeya.realRpowENN δ 2) (3 / 4) =
                Cvol.rpow (3 / 4) * ENNReal.rpow (Kakeya.realRpowENN δ 2) (3 / 4) := by
              exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
            have hdef : Cvol_pow = Cvol.rpow (3 / 4) := by rfl
            rw [h2, ←hdef] at h1
            have h3 : ENNReal.rpow (Kakeya.realRpowENN δ 2) (3 / 4) = Kakeya.realRpowENN δ (3 / 2) := by
              rw [realRpowENN_rpow_wolff hδ] <;> ring
            rw [h3] at h1
            exact h1
          have h_main_ineq : ENNReal.ofReal κ' * Kakeya.realRpowENN δ ε *
              ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4) ≤
              ENNReal.ofReal κ_h * Kakeya.realRpowENN δ (3 / 2 + ε) * ENNReal.rpow N (1 / 2) := by
            calc
              ENNReal.ofReal κ' * Kakeya.realRpowENN δ ε *
                  ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4)
                ≤ ENNReal.ofReal κ' * Kakeya.realRpowENN δ ε *
                    ENNReal.rpow N (1 / 2) * (Cvol_pow * Kakeya.realRpowENN δ (3 / 2)) := by gcongr
              _ = (ENNReal.ofReal κ' * Cvol_pow) *
                    (Kakeya.realRpowENN δ ε * Kakeya.realRpowENN δ (3 / 2)) *
                    ENNReal.rpow N (1 / 2) := by ring
              _ = (ENNReal.ofReal κ' * Cvol_pow) * Kakeya.realRpowENN δ (ε + 3 / 2) *
                    ENNReal.rpow N (1 / 2) := by
                  rw [realRpowENN_mul_wolff hδ]
              _ ≤ ENNReal.ofReal κ_h * Kakeya.realRpowENN δ (3 / 2 + ε) *
                    ENNReal.rpow N (1 / 2) := by
                  have h4 : ε + 3 / 2 = 3 / 2 + ε := by ring
                  rw [h4]
                  gcongr
          simp only [Kakeya.AssertionDLowerBound, mul_assoc]
          simp only [mul_assoc] at h_norm
          rw [h_norm]
          simpa [mul_assoc, zero_add] using h_main_ineq.trans h_hb
        · -- Case 4: δ₀ < δ ≤ 1/2 (intermediate scale, use density + KatzTao)
          have hδ_ge : δ₀ ≤ δ := by linarith
          let lam := Kakeya.realRpowENN δ η'
          have hlam_pos : 0 < lam := by
            simp [lam, Kakeya.realRpowENN] <;> positivity
          have hlam_top : lam ≠ ⊤ := by
            dsimp only [lam, Kakeya.realRpowENN]
            exact ENNReal.ofReal_ne_top
          have h_dense2 : lam * F.mass ≤ Y.mass := by
            simpa [Kakeya.Shading.IsLambdaDense] using hYDense
          rcases Finset.exists_max_image F (fun T : Kakeya.DeltaTube δ =>
              MeasureTheory.volume (Y.carrier T)) hF_nonempty with
            ⟨T, hT, hT_max⟩
          have h_sum_le : Y.mass ≤ N * MeasureTheory.volume (Y.carrier T) := by
            have h1 : Y.mass = ∑ T' ∈ F, MeasureTheory.volume (Y.carrier T') := by rfl
            rw [h1]
            have h2 : ∑ T' ∈ F, MeasureTheory.volume (Y.carrier T') ≤
                ∑ T' ∈ F, MeasureTheory.volume (Y.carrier T) := by
              apply Finset.sum_le_sum
              intro T' hT'
              exact hT_max T' hT'
            have h3 : ∑ T' ∈ F, MeasureTheory.volume (Y.carrier T) =
                N * MeasureTheory.volume (Y.carrier T) := by
              simp [N, Kakeya.TubeFamily.enncard, Finset.sum_const]
            calc
              ∑ T' ∈ F, MeasureTheory.volume (Y.carrier T')
                ≤ ∑ T' ∈ F, MeasureTheory.volume (Y.carrier T) := h2
              _ = N * MeasureTheory.volume (Y.carrier T) := h3
          have hN_mul_le : N * MeasureTheory.volume (Y.carrier T) ≥ lam * N * V := by
            have h_assoc : lam * (N * V) = lam * N * V := by
              rw [mul_assoc]
            calc
              N * MeasureTheory.volume (Y.carrier T) ≥ Y.mass := h_sum_le
              _ ≥ lam * F.mass := h_dense2
              _ = lam * (N * V) := by rw [h_mass]
              _ = lam * N * V := h_assoc
          have h_cancel : N * (lam * V) ≤ N * MeasureTheory.volume (Y.carrier T) := by
            have h_comm : lam * N * V = N * (lam * V) := by
              rw [mul_comm lam N, mul_assoc]
            rw [h_comm] at hN_mul_le
            exact hN_mul_le
          have hT_vol : lam * V ≤ MeasureTheory.volume (Y.carrier T) := by
            have h : N⁻¹ * (N * (lam * V)) ≤ N⁻¹ * (N * MeasureTheory.volume (Y.carrier T)) := by
              gcongr
            have hNinv : N⁻¹ * N = 1 := ENNReal.inv_mul_cancel hN0 hN_top
            have h' : N⁻¹ * (N * (lam * V)) = lam * V := by
              calc
                N⁻¹ * (N * (lam * V)) = (N⁻¹ * N) * (lam * V) := by rw [mul_assoc]
                _ = 1 * (lam * V) := by rw [hNinv]
                _ = lam * V := by simp
            have h'' : N⁻¹ * (N * MeasureTheory.volume (Y.carrier T)) = MeasureTheory.volume (Y.carrier T) := by
              calc
                N⁻¹ * (N * MeasureTheory.volume (Y.carrier T))
                  = (N⁻¹ * N) * MeasureTheory.volume (Y.carrier T) := by rw [mul_assoc]
                _ = 1 * MeasureTheory.volume (Y.carrier T) := by rw [hNinv]
                _ = MeasureTheory.volume (Y.carrier T) := by simp
            rw [h', h''] at h
            exact h
          have h_union : MeasureTheory.volume (Y.carrier T) ≤ MeasureTheory.volume Y.union := by
            apply MeasureTheory.measure_mono
            intro x hx
            exact ⟨T, hT, hx⟩
          have h_lower : lam * V ≤ MeasureTheory.volume Y.union := by
            calc
              lam * V ≤ MeasureTheory.volume (Y.carrier T) := hT_vol
              _ ≤ MeasureTheory.volume Y.union := h_union
          -- Convexity of unit ball
          have h_conv : Convex ℝ Kakeya.DeltaTube.unitBall := by
            dsimp only [Kakeya.DeltaTube.unitBall]
            intro x hx y hy a b ha hb hab
            have hx1 : ‖x‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
            have hy1 : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
            have h : ‖a • x + b • y‖ ≤ 1 := by
              calc
                ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
                _ = a * ‖x‖ + b * ‖y‖ := by
                  have ha_norm : ‖a‖ = a := by
                    simpa [Real.norm_eq_abs] using abs_of_nonneg ha
                  have hb_norm : ‖b‖ = b := by
                    simpa [Real.norm_eq_abs] using abs_of_nonneg hb
                  have h1 : ‖a • x‖ = a * ‖x‖ := by
                    calc ‖a • x‖ = ‖a‖ * ‖x‖ := norm_smul a x
                      _ = a * ‖x‖ := by rw [ha_norm]
                  have h2 : ‖b • y‖ = b * ‖y‖ := by
                    calc ‖b • y‖ = ‖b‖ * ‖y‖ := norm_smul b y
                      _ = b * ‖y‖ := by rw [hb_norm]
                  rw [h1, h2]
                _ ≤ a * 1 + b * 1 := by gcongr
                _ = 1 := by linarith
            simpa [Metric.mem_closedBall, dist_eq_norm] using h
          have hKT_unit := hKT Kakeya.DeltaTube.unitBall h_conv
          have h_contained : F.containedCount Kakeya.DeltaTube.unitBall = N := by
            dsimp only [N, Kakeya.TubeFamily.containedCount]
            classical
            have hfilter : F.filter (fun T : Kakeya.DeltaTube δ =>
                T.carrier ⊆ Kakeya.DeltaTube.unitBall) = F := by
              apply Finset.filter_true_of_mem
              intro T hT
              exact hFBall hT
            rw [hfilter]
            <;> rfl
          rw [h_contained] at hKT_unit
          let D := Kakeya.realRpowENN δ (-η')
          have hN_bound : N ≤ D * B * V⁻¹ := by
            simpa [D, Kakeya.realRpowENN] using hKT_unit
          have hN_mul_bound : N * V ≤ D * B := by
            calc
              N * V ≤ (D * B * V⁻¹) * V := by gcongr
              _ = D * B * (V⁻¹ * V) := by ring
              _ = D * B * 1 := by rw [ENNReal.inv_mul_cancel hV0 hV_top]
              _ = D * B := by ring
          have hN_rpow : ENNReal.rpow (N * V) (1 / 2) ≤ ENNReal.rpow (D * B) (1 / 2) :=
            ENNReal.rpow_le_rpow hN_mul_bound (by norm_num)
          have h_mul_rpow1 : ENNReal.rpow (N * V) (1 / 2) =
              ENNReal.rpow N (1 / 2) * ENNReal.rpow V (1 / 2) := by
            exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
          have h_mul_rpow2 : ENNReal.rpow (D * B) (1 / 2) =
              ENNReal.rpow D (1 / 2) * Bsqrt := by
            exact ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
          have hN_V_rpow : ENNReal.rpow N (1 / 2) * ENNReal.rpow V (1 / 2) ≤
              ENNReal.rpow D (1 / 2) * Bsqrt := by
            rw [h_mul_rpow1, h_mul_rpow2] at hN_rpow
            exact hN_rpow
          have hD_rpow : ENNReal.rpow D (1 / 2) = Kakeya.realRpowENN δ (-η' / 2) := by
            dsimp only [D]
            rw [realRpowENN_rpow_wolff hδ (-η') (1 / 2)]
            <;> ring
          have hV34 : ENNReal.rpow V (3 / 4) =
              ENNReal.rpow V (1 / 2) * ENNReal.rpow V (1 / 4) := by
            calc
              ENNReal.rpow V (3 / 4) = ENNReal.rpow V ((1 / 2) + (1 / 4)) := by norm_num
              _ = ENNReal.rpow V (1 / 2) * ENNReal.rpow V (1 / 4) :=
                ENNReal.rpow_add (x := V) (1 / 2) (1 / 4) hV0 hV_top
          have hV_lower : V ≥ Kakeya.realRpowENN δ 2 := by
            have h1 : ENNReal.ofReal (δ ^ 2) ≤ V := canonical_volume_lower hδ
            have h2 : Kakeya.realRpowENN δ 2 = ENNReal.ofReal (δ ^ 2) := by
              simp [Kakeya.realRpowENN]
            rw [h2]
            exact h1
          have hV_rpow_lower : ENNReal.rpow V (3 / 4) ≥ Kakeya.realRpowENN δ (3 / 2) := by
            have h1 : ENNReal.rpow V (3 / 4) ≥ ENNReal.rpow (Kakeya.realRpowENN δ 2) (3 / 4) :=
              ENNReal.rpow_le_rpow hV_lower (by norm_num)
            have h2 : ENNReal.rpow (Kakeya.realRpowENN δ 2) (3 / 4) = Kakeya.realRpowENN δ (3 / 2) := by
              rw [realRpowENN_rpow_wolff hδ] <;> ring
            rw [h2] at h1
            exact h1
          have hC_bound : C ≤ Kakeya.realRpowENN δ β := by
            dsimp only [C, β]
            by_cases hβ : β ≥ 0
            · rw [if_pos hβ]
              exact helper_realRpowENN_mono hδ₀ hδ_ge hβ
            · rw [if_neg hβ]
              have hβ' : β ≤ 0 := by linarith
              exact helper_realRpowENN_anti hδ hδ_le_half hβ'
          have h_chain1 : ENNReal.ofReal κ' * Bsqrt ≤
              Kakeya.realRpowENN δ (3 * η' / 2 - ε) * ENNReal.rpow V (3 / 4) := by
            calc
              ENNReal.ofReal κ' * Bsqrt ≤ C := h_case4
              _ ≤ Kakeya.realRpowENN δ β := hC_bound
              _ = Kakeya.realRpowENN δ (3 * η' / 2 - ε) * Kakeya.realRpowENN δ (3 / 2) := by
                    dsimp only [β]
                    rw [← realRpowENN_mul_wolff hδ]
              _ ≤ Kakeya.realRpowENN δ (3 * η' / 2 - ε) * ENNReal.rpow V (3 / 4) := by
                  exact mul_le_mul_of_nonneg_left hV_rpow_lower (by simp)
          have h_final : ENNReal.ofReal κ' * Kakeya.realRpowENN δ ε *
              ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4) ≤ lam * V := by
            calc
              ENNReal.ofReal κ' * Kakeya.realRpowENN δ ε *
                  ENNReal.rpow N (1 / 2) * ENNReal.rpow V (3 / 4)
                = ENNReal.ofReal κ' * Kakeya.realRpowENN δ ε *
                    (ENNReal.rpow N (1 / 2) * ENNReal.rpow V (1 / 2)) *
                    ENNReal.rpow V (1 / 4) := by
                  rw [hV34] <;> ring
              _ ≤ ENNReal.ofReal κ' * Kakeya.realRpowENN δ ε *
                    (ENNReal.rpow D (1 / 2) * Bsqrt) * ENNReal.rpow V (1 / 4) := by
                  gcongr
              _ = ENNReal.ofReal κ' * Bsqrt *
                    (Kakeya.realRpowENN δ ε * Kakeya.realRpowENN δ (-η' / 2)) *
                    ENNReal.rpow V (1 / 4) := by
                  rw [hD_rpow] <;> ring
              _ = ENNReal.ofReal κ' * Bsqrt *
                    Kakeya.realRpowENN δ (ε - η' / 2) * ENNReal.rpow V (1 / 4) := by
                  rw [realRpowENN_mul_wolff hδ]
                  have h_exp : ε + (-η' / 2) = ε - η' / 2 := by ring
                  rw [h_exp]
              _ ≤ (Kakeya.realRpowENN δ (3 * η' / 2 - ε) * ENNReal.rpow V (3 / 4)) *
                    Kakeya.realRpowENN δ (ε - η' / 2) * ENNReal.rpow V (1 / 4) := by
                  gcongr
              _ = Kakeya.realRpowENN δ ((3 * η' / 2 - ε) + (ε - η' / 2)) *
                    (ENNReal.rpow V (3 / 4) * ENNReal.rpow V (1 / 4)) := by
                  have h_rpow_mul : Kakeya.realRpowENN δ (3 * η' / 2 - ε) * Kakeya.realRpowENN δ (ε - η' / 2) =
                      Kakeya.realRpowENN δ ((3 * η' / 2 - ε) + (ε - η' / 2)) :=
                    realRpowENN_mul_wolff hδ
                  have h_rearrange :
                      (Kakeya.realRpowENN δ (3 * η' / 2 - ε) * ENNReal.rpow V (3 / 4)) *
                          Kakeya.realRpowENN δ (ε - η' / 2) * ENNReal.rpow V (1 / 4) =
                      (Kakeya.realRpowENN δ (3 * η' / 2 - ε) * Kakeya.realRpowENN δ (ε - η' / 2)) *
                          (ENNReal.rpow V (3 / 4) * ENNReal.rpow V (1 / 4)) := by
                    simp [mul_assoc, mul_comm]
                  rw [h_rearrange, h_rpow_mul]
              _ = Kakeya.realRpowENN δ η' * V := by
                    have h_exp : (3 * η' / 2 - ε) + (ε - η' / 2) = η' := by ring
                    have hV_add : ENNReal.rpow V (3 / 4) * ENNReal.rpow V (1 / 4) = V := by
                      calc
                        ENNReal.rpow V (3 / 4) * ENNReal.rpow V (1 / 4)
                          = ENNReal.rpow V ((3 / 4) + (1 / 4)) :=
                            (ENNReal.rpow_add (x := V) (3 / 4) (1 / 4) hV0 hV_top).symm
                        _ = ENNReal.rpow V 1 := by norm_num
                        _ = V := ENNReal.rpow_one V
                    rw [h_exp, hV_add]
          simp only [Kakeya.AssertionDLowerBound, mul_assoc]
          have h_norm2 := assertionD_normalization_eq_wolff F.enncard (deltaTubeVolume δ) hN0 hN_top hV0 hV_top
          simp only [mul_assoc] at h_norm2
          rw [h_norm2]
          simpa [mul_assoc, zero_add] using h_final.trans h_lower
  exact h_assertionD

end Kakeya.Assouad
