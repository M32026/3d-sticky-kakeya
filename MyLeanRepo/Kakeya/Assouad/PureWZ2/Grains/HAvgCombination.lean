import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgMassLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HAvgExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# h_avg combination lemma

Combines the mass lower bound, volume upper bound, and exponent arithmetic
to prove `m * volume < mass / 2`.

This gives ≥ 1/2 mass retention for the high-multiplicity set:
`mass(high) = mass - mass(low) ≥ mass - m*volume > mass/2 > mass/8`,
so K=8 works for extremal transfer.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory ENNReal

/-- Combine mass lower bound, volume upper bound, and exponent arithmetic
to prove `m * volume < mass / 2`.

This gives ≥ 1/2 mass retention for the high-multiplicity set:
`mass(high) = mass - mass(low) ≥ mass - m*volume > mass/2 > mass/8`,
so K=8 works for extremal transfer. -/
lemma h_avg_from_extremal_line_class
    {sigma stickyLoss L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma stickyLoss coarse coarseShading)
    (hline : WZ1PaperIsLineClass coarse)
    (m : ℕ)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 24)
    (hm_bound : (m : ℝ) * L ^ (sigma - 3 * stickyLoss) < 1 / 8) :
    (m : ENNReal) * MeasureTheory.volume coarseShading.union < (1 / 2 : ENNReal) * coarseShading.mass := by
  -- Step 1: Mass lower bound
  have h_mass_lower : (1 / 4 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss) ≤
      coarseShading.mass :=
    coarse_shading_mass_lower_bound_of_line_class
      coarseExtremal hline hL_pos hL_small

  -- Step 2: Volume upper bound
  have h_vol : MeasureTheory.volume coarseShading.union ≤
      Kakeya.realRpowENN L (sigma - stickyLoss) :=
    coarseExtremal.volume_upper

  -- Step 3: Exponent split
  have h_exp_split : Kakeya.realRpowENN L (sigma - stickyLoss) =
      Kakeya.realRpowENN L (sigma - 3 * stickyLoss) *
      Kakeya.realRpowENN L (2 * stickyLoss) := by
    simp only [Kakeya.realRpowENN]
    have h_add : (sigma - 3 * stickyLoss) + (2 * stickyLoss) = sigma - stickyLoss := by ring
    have h_real : Real.rpow L (sigma - stickyLoss) =
        Real.rpow L (sigma - 3 * stickyLoss) * Real.rpow L (2 * stickyLoss) := by
      have h : Real.rpow L ((sigma - 3 * stickyLoss) + (2 * stickyLoss)) =
          Real.rpow L (sigma - 3 * stickyLoss) * Real.rpow L (2 * stickyLoss) :=
        Real.rpow_add hL_pos _ _
      rw [h_add] at h
      exact h
    rw [h_real]
    have h_pos1 : 0 ≤ Real.rpow L (sigma - 3 * stickyLoss) := Real.rpow_nonneg hL_pos.le _
    exact ENNReal.ofReal_mul h_pos1

  -- Step 4: Convert m bound to ENNReal
  have h_nonneg1 : 0 ≤ (m : ℝ) := by positivity
  have h_m_ennreal : (m : ENNReal) * Kakeya.realRpowENN L (sigma - 3 * stickyLoss) =
      ENNReal.ofReal ((m : ℝ) * L ^ (sigma - 3 * stickyLoss)) := by
    have h_m_coe : (m : ENNReal) = ENNReal.ofReal (m : ℝ) := by simp
    rw [h_m_coe]
    simp only [Kakeya.realRpowENN]
    have h : ENNReal.ofReal (m : ℝ) * ENNReal.ofReal (L ^ (sigma - 3 * stickyLoss)) =
        ENNReal.ofReal ((m : ℝ) * L ^ (sigma - 3 * stickyLoss)) := by
      rw [← ENNReal.ofReal_mul h_nonneg1] <;> rfl
    exact h
  have h_m_lt : (m : ENNReal) * Kakeya.realRpowENN L (sigma - 3 * stickyLoss) <
      (1 / 8 : ENNReal) := by
    rw [h_m_ennreal]
    have h_pos_eighth : (0 : ℝ) < 1 / 8 := by norm_num
    have h_lt : ENNReal.ofReal ((m : ℝ) * L ^ (sigma - 3 * stickyLoss)) <
        ENNReal.ofReal (1 / 8 : ℝ) := by
      rw [ENNReal.ofReal_lt_ofReal_iff h_pos_eighth]
      exact hm_bound
    simpa using h_lt

  -- Step 5: Combine
  have h_main1 : (m : ENNReal) * MeasureTheory.volume coarseShading.union ≤
      (m : ENNReal) * Kakeya.realRpowENN L (sigma - stickyLoss) := by
    gcongr
  have h_main2 : (m : ENNReal) * Kakeya.realRpowENN L (sigma - stickyLoss) =
      ((m : ENNReal) * Kakeya.realRpowENN L (sigma - 3 * stickyLoss)) *
      Kakeya.realRpowENN L (2 * stickyLoss) := by
    rw [h_exp_split, mul_assoc]
  have h_pos : 0 < Kakeya.realRpowENN L (2 * stickyLoss) := by
    have h1 : 0 < L ^ (2 * stickyLoss) := Real.rpow_pos_of_pos hL_pos _
    simpa [Kakeya.realRpowENN, ENNReal.ofReal_pos] using h1
  have h_ne_zero : Kakeya.realRpowENN L (2 * stickyLoss) ≠ 0 := h_pos.ne'
  have h_ne_top : Kakeya.realRpowENN L (2 * stickyLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have h_main3 : ((m : ENNReal) * Kakeya.realRpowENN L (sigma - 3 * stickyLoss)) *
      Kakeya.realRpowENN L (2 * stickyLoss) <
      (1 / 8 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss) :=
    ENNReal.mul_lt_mul_left h_ne_zero h_ne_top h_m_lt
  have h5 : (1 / 8 : ENNReal) = (1 / 2 : ENNReal) * (1 / 4 : ENNReal) := by
    have h_ne_top1 : (1 / 8 : ENNReal) ≠ ⊤ := by simp
    have h_ne_top2 : ((1 / 2 : ENNReal) * (1 / 4 : ENNReal)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) (by simp)
    have h_eq : ENNReal.toReal (1 / 8 : ENNReal) =
        ENNReal.toReal ((1 / 2 : ENNReal) * (1 / 4 : ENNReal)) := by
      simp [ENNReal.toReal_mul]
      <;> norm_num
    exact (ENNReal.toReal_eq_toReal_iff' h_ne_top1 h_ne_top2).mp h_eq
  have h_main4 : (1 / 8 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss) ≤
      (1 / 2 : ENNReal) * coarseShading.mass := by
    calc
      (1 / 8 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss)
        = ((1 / 2 : ENNReal) * (1 / 4 : ENNReal)) * Kakeya.realRpowENN L (2 * stickyLoss) := by
          rw [h5]
      _ = (1 / 2 : ENNReal) * ((1 / 4 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss)) := by
          rw [mul_assoc]
      _ ≤ (1 / 2 : ENNReal) * coarseShading.mass := by
          exact mul_le_mul_left' h_mass_lower (1 / 2 : ENNReal)
  calc (m : ENNReal) * MeasureTheory.volume coarseShading.union
    ≤ (m : ENNReal) * Kakeya.realRpowENN L (sigma - stickyLoss) := h_main1
  _ = ((m : ENNReal) * Kakeya.realRpowENN L (sigma - 3 * stickyLoss)) *
        Kakeya.realRpowENN L (2 * stickyLoss) := h_main2
  _ < (1 / 8 : ENNReal) * Kakeya.realRpowENN L (2 * stickyLoss) := h_main3
  _ ≤ (1 / 2 : ENNReal) * coarseShading.mass := h_main4

/-- Backwards-compatible wrapper for a Section 6 cover. -/
lemma h_avg_from_sticky
    {sigma stickyLoss L delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma stickyLoss coarse coarseShading)
    (cover : PureWZ2Section6Cover fine coarse)
    (m : ℕ)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 24)
    (hm_bound : (m : ℝ) * L ^ (sigma - 3 * stickyLoss) < 1 / 8) :
    (m : ENNReal) * MeasureTheory.volume coarseShading.union <
      (1 / 2 : ENNReal) * coarseShading.mass :=
  h_avg_from_extremal_line_class coarseExtremal
    cover.coarse_line_class m hL_pos hL_small hm_bound

end Kakeya.Assouad.PureWZ2

end
