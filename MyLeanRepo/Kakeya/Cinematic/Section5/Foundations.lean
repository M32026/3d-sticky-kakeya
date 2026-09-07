import MyLeanRepo.Kakeya.Cinematic.Statements
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Section 5 analytic foundations

This module contains the closed selection and restricted weak-type reduction
arguments used at the start of PYZ Section 5.
-/

namespace Kakeya.Cinematic

open MeasureTheory

theorem restricted_weak_type_reduction :
    RestrictedWeakTypeReductionStatement := by
  intro hselect
  refine ⟨4, by norm_num, ?_⟩
  intro delta B hdelta hB F E hE hE_finite hlevel
  rcases hselect delta hdelta F E hE hE_finite with htotal | hselected
  · rw [htotal]
    positivity
  · obtain ⟨mu, hmu, E₀, hE₀, hE₀_subset, hmultiplicity, htotal⟩ := hselected
    have hE₀_finite : volume E₀ < ⊤ :=
      lt_of_le_of_lt (measure_mono hE₀_subset) hE_finite
    have hpointwise : ∀ p ∈ E₀,
        ‖Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)‖ ≤
          Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) := by
      intro p hp
      have hm_nonneg : 0 ≤ multiplicity F delta p := by
        dsimp only [multiplicity]
        apply Finset.sum_nonneg
        intro f _
        exact Set.indicator_nonneg (fun _ => by norm_num) _
      rw [Real.norm_eq_abs]
      have hrpow_nonneg :
          0 ≤ Real.rpow (multiplicity F delta p) (3 / 2 : ℝ) :=
        Real.rpow_nonneg hm_nonneg _
      rw [abs_of_nonneg hrpow_nonneg]
      exact Real.rpow_le_rpow hm_nonneg (le_of_lt (hmultiplicity p hp).2) (by norm_num)
    have hintegral_measure :
        (∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤
          Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) * volume.real E₀ := by
      calc
        (∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤
            ‖∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)‖ := by
          simpa only [Real.norm_eq_abs] using
            le_abs_self (∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ))
        _ ≤ Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) * volume.real E₀ :=
          norm_setIntegral_le_of_norm_le_const hE₀_finite hpointwise
    have hmeasure := hlevel mu hmu E₀ hE₀ hE₀_subset hmultiplicity
    have hmeasure_real :
        volume.real E₀ ≤ B * Real.rpow (mu : ℝ) (-3 / 2 : ℝ) := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg hB (Real.rpow_nonneg (by positivity) _)) hmeasure
    have hconstant_nonneg :
        0 ≤ Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have hintegral_level :
        (∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤
          Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) *
            (B * Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) :=
      hintegral_measure.trans (mul_le_mul_of_nonneg_left hmeasure_real hconstant_nonneg)
    have hmu_real : 0 < (mu : ℝ) := by exact_mod_cast hmu
    have hmul_rpow :
        Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) =
          Real.rpow 2 (3 / 2 : ℝ) * Real.rpow (mu : ℝ) (3 / 2 : ℝ) :=
      Real.mul_rpow (by norm_num) hmu_real.le
    have hmu_power_ne : Real.rpow (mu : ℝ) (3 / 2 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hmu_real _).ne'
    have hmu_neg :
        Real.rpow (mu : ℝ) (-(3 / 2 : ℝ)) =
          (Real.rpow (mu : ℝ) (3 / 2 : ℝ))⁻¹ :=
      Real.rpow_neg hmu_real.le _
    have hmu_cancel :
        Real.rpow (mu : ℝ) (3 / 2 : ℝ) *
            Real.rpow (mu : ℝ) (-3 / 2 : ℝ) = 1 := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, hmu_neg]
      exact mul_inv_cancel₀ hmu_power_ne
    have hcancel :
        Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) *
              (B * Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) =
            Real.rpow 2 (3 / 2 : ℝ) * B := by
      rw [hmul_rpow]
      calc
        (Real.rpow 2 (3 / 2 : ℝ) * Real.rpow (mu : ℝ) (3 / 2 : ℝ)) *
              (B * Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) =
            Real.rpow 2 (3 / 2 : ℝ) * B *
              (Real.rpow (mu : ℝ) (3 / 2 : ℝ) *
                Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := by ring
        _ = Real.rpow 2 (3 / 2 : ℝ) * B := by rw [hmu_cancel, mul_one]
    have htwo_power : Real.rpow 2 (3 / 2 : ℝ) ≤ 4 := by
      calc
        Real.rpow 2 (3 / 2 : ℝ) ≤ Real.rpow 2 2 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 4 := by norm_num
    have hintegral_bound :
        (∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤ 4 * B := by
      calc
        (∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤
            Real.rpow (2 * (mu : ℝ)) (3 / 2 : ℝ) *
              (B * Real.rpow (mu : ℝ) (-3 / 2 : ℝ)) := hintegral_level
        _ = Real.rpow 2 (3 / 2 : ℝ) * B := hcancel
        _ ≤ 4 * B := mul_le_mul_of_nonneg_right htwo_power hB
    have hlevels_nonneg :
        0 ≤ (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) := by positivity
    calc
      (∫ p in E, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ)) ≤
          (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) *
            ∫ p in E₀, Real.rpow (multiplicity F delta p) (3 / 2 : ℝ) := htotal
      _ ≤ (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) * (4 * B) :=
        mul_le_mul_of_nonneg_left hintegral_bound hlevels_nonneg
      _ = 4 * (((Nat.log2 (F.card + 1) + 1 : ℕ) : ℝ)) * B := by ring

end Kakeya.Cinematic
