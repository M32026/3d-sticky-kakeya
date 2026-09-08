/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic

/-!
# Volume bounds for tubes

This file records consequences of the general volume estimates for tubes.
-/

@[expose] public section

open MeasureTheory

namespace Kakeya
namespace Tube

/-- The dimensional constant in `volume_cthickening_unit_segment_le`. -/
noncomputable def unitSegmentCthickeningVolumeConstant
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NNReal :=
  Tube.volume_le.C (Module.finrank ℝ E)

lemma unitSegmentCthickeningVolumeConstant_pos
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    0 < unitSegmentCthickeningVolumeConstant E := by
  exact Tube.volume_le.C_pos _

/-- The volume of the `r`-neighborhood of a unit segment is at most a dimensional
constant times `r ^ (n - 1)`. -/
lemma volume_cthickening_unit_segment_le
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (x y : E) (hxy : dist x y = 1) (r : NNReal) (hr1 : r ≤ 1) :
    volume (Metric.cthickening (r : ℝ) (segment ℝ x y)) ≤
      (unitSegmentCthickeningVolumeConstant E : ENNReal) *
        (r : ENNReal) ^ (Module.finrank ℝ E - 1) := by
  letI : ProperSpace E := FiniteDimensional.proper_real E
  let T : Tube r E := Tube.mk' r hxy
  have hcarrier : T.carrier = Metric.cthickening (r : ℝ) (segment ℝ x y) := by
    simpa [T] using T.carrier_eq_cthickening
  rw [← hcarrier]
  exact Tube.volume_le hr1 T

end Tube
end Kakeya

namespace Tube

open ENNReal Metric in
/-- If `T : Tube δ E` with `δ ≤ 4` and `ρ ≤ δ`, then the volume of the
`ρ`-cthickening of `T.carrier` is bounded by a uniform constant times `δ^(n-1)`.

The bound is stated up to scale `4` rather than `1` because the prefix-offset chain of GWZ
Lemma 7.5 lives at the fattened scales `3 * ρ k`, whose coarsest value is `3`. -/
lemma volume_cthickening_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] :
    ∃ M' : NNReal, 0 < M' ∧ ∀ (δ : NNReal), 0 < δ → δ ≤ 4 →
      ∀ (ρ : NNReal), ρ ≤ δ →
      ∀ T : Tube δ E,
        volume (Metric.cthickening (ρ : ℝ) T.carrier)
          ≤ M' * δ ^ (Module.finrank ℝ E - 1) := by
  set n := Module.finrank ℝ E
  set M : ℝ := (volume_le.C n : ℝ) with hM_def
  have hM_pos : 0 < M := by
    change (0 : ℝ) < ((volume_le.C n : NNReal) : ℝ)
    unfold volume_le.C
    push_cast
    positivity
  have hM : ∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ T : Tube δ E,
      volume.real T.carrier ≤ M * (δ : ℝ) ^ (n - 1) := by
    intro δ hδ hδ1 T
    have h := volume_le hδ1 T
    have hRHS_fin : (volume_le.C n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_fin h
    simpa [hM_def, ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_pow,
      MeasureTheory.Measure.real] using hreal
  set V : ℝ := Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1) with hV_def
  have hV_pos : 0 < V := by rw [hV_def]; positivity
  set Mr : ℝ := max (M * 2 ^ (n - 1)) (V * 9 ^ n * 2 ^ (n - 1)) with hMr_def
  have hMr_pos : 0 < Mr :=
    lt_of_lt_of_le (mul_pos hM_pos (by positivity)) (le_max_left _ _)
  set MrN : NNReal := ⟨Mr, hMr_pos.le⟩ with hMrN_def
  have hMrN_pos : (0 : NNReal) < MrN := by
    rw [← NNReal.coe_lt_coe]; exact hMr_pos
  refine ⟨MrN, hMrN_pos, ?_⟩
  intro δ hδ hδ1 ρ hρ_le_δ T
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hρr_nn : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hρr_le_δr : (ρ : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hρ_le_δ
  have hδρ_pos : (0 : ℝ) < (δ : ℝ) + (ρ : ℝ) := by linarith
  have hδρ_le_2δ : (δ : ℝ) + (ρ : ℝ) ≤ 2 * (δ : ℝ) := by linarith
  have h_le : δ ≤ δ + ρ := by
    have : (0 : NNReal) ≤ ρ := bot_le
    exact le_add_of_nonneg_right this
  have hδρ_pos_nn : 0 < δ + ρ := by
    rw [← NNReal.coe_pos]; push_cast; linarith
  have h_eq : Metric.cthickening (ρ : ℝ) T.carrier = (T.rescale (δ + ρ)).carrier := by
    have h_carrier : (T.rescale (δ + ρ)).carrier
        = ⋃ z ∈ segment ℝ T.x T.y, Metric.closedBall z ((δ : ℝ) + (ρ : ℝ)) := by
      change (⋃ z ∈ segment ℝ T.x T.y, Metric.closedBall z (((δ + ρ : NNReal) : ℝ)))
          = ⋃ z ∈ segment ℝ T.x T.y, Metric.closedBall z ((δ : ℝ) + (ρ : ℝ))
      push_cast; rfl
    rw [h_carrier, T.carrier_eq,
        ← isCompact_segment.cthickening_eq_biUnion_closedBall δ.coe_nonneg,
        cthickening_cthickening ρ.coe_nonneg δ.coe_nonneg,
        show (ρ : ℝ) + (δ : ℝ) = (δ : ℝ) + (ρ : ℝ) from add_comm _ _,
        isCompact_segment.cthickening_eq_biUnion_closedBall
          (by positivity : (0 : ℝ) ≤ (δ : ℝ) + (ρ : ℝ))]
  set T' : Tube (δ + ρ) E := T.rescale (δ + ρ) with hT'_def
  have hreal : volume.real T'.carrier ≤ Mr * (δ : ℝ) ^ (n - 1) := by
    by_cases hcase : (δ : ℝ) + (ρ : ℝ) ≤ 1
    · have hcase_nn : δ + ρ ≤ 1 := by
        rw [← NNReal.coe_le_coe]; push_cast; exact hcase
      have h_T'_bound : volume.real T'.carrier ≤ M * ((δ : ℝ) + (ρ : ℝ)) ^ (n - 1) := by
        have := hM (δ + ρ) hδρ_pos_nn hcase_nn T'
        simpa [NNReal.coe_add] using this
      have h_pow_le : ((δ : ℝ) + (ρ : ℝ)) ^ (n - 1) ≤ (2 * (δ : ℝ)) ^ (n - 1) :=
        pow_le_pow_left₀ hδρ_pos.le hδρ_le_2δ _
      have h_step : (2 * (δ : ℝ)) ^ (n - 1) = 2 ^ (n - 1) * (δ : ℝ) ^ (n - 1) := by
        rw [mul_pow]
      calc volume.real T'.carrier
          ≤ M * ((δ : ℝ) + (ρ : ℝ)) ^ (n - 1) := h_T'_bound
        _ ≤ M * (2 * (δ : ℝ)) ^ (n - 1) :=
            mul_le_mul_of_nonneg_left h_pow_le hM_pos.le
        _ = M * 2 ^ (n - 1) * (δ : ℝ) ^ (n - 1) := by rw [h_step]; ring
        _ ≤ Mr * (δ : ℝ) ^ (n - 1) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hδr.le _)
    · have hcase' : 1 < (δ : ℝ) + (ρ : ℝ) := lt_of_not_ge hcase
      have hδ_gt_half : 1/2 < (δ : ℝ) := by linarith
      have hδ_pow_lb : (1/2 : ℝ) ^ (n - 1) ≤ (δ : ℝ) ^ (n - 1) :=
        pow_le_pow_left₀ (by norm_num) hδ_gt_half.le _
      have h_T'_subset : T'.carrier ⊆ Metric.closedBall T.x (1 + ((δ : ℝ) + (ρ : ℝ))) := by
        rw [T'.carrier_eq]
        intro p hp
        obtain ⟨w, hw_seg, hpw⟩ := Set.mem_iUnion₂.mp hp
        rw [Metric.mem_closedBall]
        have hw_dist : dist w T.x ≤ 1 := by
          obtain ⟨a, b, ha, hb, hab, hw_eq⟩ := hw_seg
          have hT'x : T'.x = T.x := rfl
          have hT'y : T'.y = T.y := rfl
          rw [hT'x, hT'y] at hw_eq
          rw [dist_eq_norm, ← hw_eq,
              show a • T.x + b • T.y - T.x = b • (T.y - T.x) by
                have ha_eq : a = 1 - b := by linarith
                rw [ha_eq, sub_smul, one_smul]; module,
              norm_smul, Real.norm_of_nonneg hb,
              show ‖T.y - T.x‖ = 1 by
                rw [← dist_eq_norm, dist_comm]; exact T.dist_eq_one]
          linarith
        have hpw' : dist p w ≤ ((δ + ρ : NNReal) : ℝ) := hpw
        have hpw'' : dist p w ≤ (δ : ℝ) + (ρ : ℝ) := by
          rw [NNReal.coe_add] at hpw'; exact hpw'
        calc dist p T.x ≤ dist p w + dist w T.x := dist_triangle _ _ _
          _ ≤ ((δ : ℝ) + (ρ : ℝ)) + 1 := by linarith
          _ = 1 + ((δ : ℝ) + (ρ : ℝ)) := by ring
      have h_ball_fin : volume (Metric.closedBall T.x (1 + ((δ : ℝ) + (ρ : ℝ)))) ≠ ∞ :=
        (isCompact_closedBall _ _).measure_lt_top.ne
      have h_vol_le_ball : volume.real T'.carrier ≤
          volume.real (Metric.closedBall T.x (1 + ((δ : ℝ) + (ρ : ℝ)))) :=
        measureReal_mono h_T'_subset h_ball_fin
      have h_ball_vol : volume.real (Metric.closedBall T.x (1 + ((δ : ℝ) + (ρ : ℝ))))
          = (1 + ((δ : ℝ) + (ρ : ℝ))) ^ n * V := by
        have h_pos : 0 ≤ 1 + ((δ : ℝ) + (ρ : ℝ)) := by linarith
        rw [measureReal_def, InnerProductSpace.volume_closedBall]
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal h_pos, ENNReal.toReal_ofReal hV_pos.le]
      have h_one_plus_le_nine : 1 + ((δ : ℝ) + (ρ : ℝ)) ≤ 9 := by
        have hδr4 : (δ : ℝ) ≤ 4 := by exact_mod_cast hδ1
        nlinarith
      have h_pow_le : (1 + ((δ : ℝ) + (ρ : ℝ))) ^ n ≤ 9 ^ n :=
        pow_le_pow_left₀ (by linarith) h_one_plus_le_nine _
      calc volume.real T'.carrier
          ≤ (1 + ((δ : ℝ) + (ρ : ℝ))) ^ n * V := by rw [← h_ball_vol]; exact h_vol_le_ball
        _ ≤ 9 ^ n * V := mul_le_mul_of_nonneg_right h_pow_le hV_pos.le
        _ = V * 9 ^ n := by ring
        _ = V * 9 ^ n * (2 ^ (n - 1) * (1/2 : ℝ) ^ (n - 1)) := by
            have h2half : ((2 : ℝ) ^ (n - 1) * (1/2) ^ (n - 1)) = 1 := by
              rw [← mul_pow, show (2 : ℝ) * (1/2) = 1 by norm_num, one_pow]
            rw [h2half]; ring
        _ = V * 9 ^ n * 2 ^ (n - 1) * (1/2 : ℝ) ^ (n - 1) := by ring
        _ ≤ V * 9 ^ n * 2 ^ (n - 1) * (δ : ℝ) ^ (n - 1) :=
            mul_le_mul_of_nonneg_left hδ_pow_lb (by positivity)
        _ ≤ Mr * (δ : ℝ) ^ (n - 1) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hδr.le _)
  rw [h_eq]
  have h_fin : volume T'.carrier ≠ ⊤ := T'.isCompact.measure_lt_top.ne
  have hMr_nn : (0 : ℝ) ≤ Mr := hMr_pos.le
  have hδpow_nn : (0 : ℝ) ≤ (δ : ℝ) ^ (n - 1) := pow_nonneg hδr.le _
  have h_ofReal :
      ENNReal.ofReal (volume.real T'.carrier) ≤ ENNReal.ofReal (Mr * (δ : ℝ) ^ (n - 1)) :=
    ENNReal.ofReal_le_ofReal hreal
  have h_lhs_eq :
      ENNReal.ofReal (volume.real T'.carrier) = volume T'.carrier := by
    rw [MeasureTheory.Measure.real, ENNReal.ofReal_toReal h_fin]
  have hMrN_coe : ((MrN : NNReal) : ℝ) = Mr := rfl
  have h_rhs_eq :
      ENNReal.ofReal (Mr * (δ : ℝ) ^ (n - 1))
        = (MrN : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (n - 1) := by
    rw [ENNReal.ofReal_mul hMr_nn, ENNReal.ofReal_pow hδr.le]
    congr 1
    · rw [← hMrN_coe, ENNReal.ofReal_coe_nnreal]
    · rw [ENNReal.ofReal_coe_nnreal]
  rw [← h_lhs_eq]
  calc ENNReal.ofReal (volume.real T'.carrier)
      ≤ ENNReal.ofReal (Mr * (δ : ℝ) ^ (n - 1)) := h_ofReal
    _ = (MrN : ℝ≥0∞) * (δ : ℝ≥0∞) ^ (n - 1) := h_rhs_eq

end Tube
