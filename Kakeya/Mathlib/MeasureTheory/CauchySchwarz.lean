/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Cauchy-Schwarz inequalities
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Discrete Cauchy--Schwarz lower bound for the `L²` mass associated to a
finite finset-indexed family of measurable subsets, stated for the
`ENNReal`-valued `volume`.

For a finite family `(Y i)_{i ∈ s}` of measurable subsets of a measure space
`F`,
`(∑_i |Y i|)^2 ≤ |⋃ i Y i| · (∑_{i,j} |Y i ∩ Y j|)`.

The proof uses the multiplicity function `m(x) = ∑_i 1_{Y i}(x)`, identifies
`∫ m = ∑_i |Y i|` and `∫ m² = ∑_{i,j} |Y i ∩ Y j|`, and applies Hölder's
inequality with `p = q = 2` to `1_U · m`. -/
theorem MeasureTheory.sq_sum_volume_le
    {ι F : Type*} [MeasureSpace F]
    {s : Finset ι} {Y : ι → Set F}
    (hmeas : ∀ i ∈ s, MeasurableSet (Y i)) :
    (∑ i ∈ s, volume (Y i)) ^ 2
      ≤ volume (⋃ i ∈ s, Y i)
        * (∑ i ∈ s, ∑ j ∈ s, volume (Y i ∩ Y j)) := by
  classical
  set U : Set F := ⋃ i ∈ s, Y i
  have hU_meas : MeasurableSet U := Finset.measurableSet_biUnion _ hmeas
  set m : F → ENNReal := fun x => ∑ i ∈ s, (Y i).indicator 1 x
  have hind_meas : ∀ i ∈ s, Measurable ((Y i).indicator (1 : F → ENNReal)) :=
    fun i hi => measurable_const.indicator (hmeas i hi)
  have hm_meas : Measurable m := Finset.measurable_sum s hind_meas
  have h_lintegral_m :
      ∫⁻ x, m x ∂(volume : Measure F) = ∑ i ∈ s, volume (Y i) := by
    rw [MeasureTheory.lintegral_finsetSum _ hind_meas]
    exact Finset.sum_congr rfl fun i hi =>
      MeasureTheory.lintegral_indicator_one (hmeas i hi)
  have hm_sq_eq :
      (fun x => m x ^ 2) = fun x =>
        ∑ i ∈ s, ∑ j ∈ s, (Y i ∩ Y j).indicator 1 x := by
    funext x
    simp_rw [sq, m, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simpa [Pi.one_def] using (Set.inter_indicator_mul (1 : F → ENNReal) 1 x).symm
  have h_lintegral_msq :
      ∫⁻ x, m x ^ 2 ∂(volume : Measure F)
        = ∑ i ∈ s, ∑ j ∈ s, volume (Y i ∩ Y j) := by
    have hinter : ∀ i ∈ s, ∀ j ∈ s,
        Measurable ((Y i ∩ Y j).indicator (1 : F → ENNReal)) :=
      fun i hi j hj => measurable_const.indicator ((hmeas i hi).inter (hmeas j hj))
    rw [hm_sq_eq, MeasureTheory.lintegral_finsetSum _
      (fun i hi => Finset.measurable_sum _ (hinter i hi))]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.lintegral_finsetSum _ (hinter i hi)]
    exact Finset.sum_congr rfl fun j hj =>
      MeasureTheory.lintegral_indicator_one ((hmeas i hi).inter (hmeas j hj))
  have h_eq_indicator :
      ∫⁻ x, m x ∂(volume : Measure F)
        = ∫⁻ x, U.indicator (1 : F → ENNReal) x * m x ∂(volume : Measure F) := by
    refine MeasureTheory.lintegral_congr fun x => ?_
    by_cases hx : x ∈ U
    · simp [hx]
    · have hm_zero : m x = 0 :=
        Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem
          (fun h : x ∈ Y i => hx (Set.mem_biUnion hi h)) _
      simp [Set.indicator_of_notMem hx, hm_zero]
  have hCS_lintegral :
      (∫⁻ x, U.indicator (1 : F → ENNReal) x * m x ∂(volume : Measure F)) ^ 2
        ≤ (∫⁻ x, U.indicator (1 : F → ENNReal) x ^ 2 ∂(volume : Measure F))
          * (∫⁻ x, m x ^ 2 ∂(volume : Measure F)) := by
    have hf_meas : AEMeasurable (U.indicator (1 : F → ENNReal)) (volume : Measure F) :=
      (measurable_const.indicator hU_meas).aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure F)
      Real.HolderConjugate.two_two hf_meas hm_meas.aemeasurable
    simp only [Pi.mul_apply, ENNReal.rpow_two] at hH
    have hH_sq := pow_le_pow_left₀ zero_le hH 2
    have hpow : ∀ a : ENNReal, (a ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = a := fun a => by
      rw [one_div]; exact ENNReal.rpow_inv_natCast_pow (by norm_num) a
    rwa [mul_pow, hpow, hpow] at hH_sq
  have h_integral_U :
      ∫⁻ x, U.indicator (1 : F → ENNReal) x ^ 2 ∂(volume : Measure F)
        = volume U := by
    have hpt : (fun x => U.indicator (1 : F → ENNReal) x ^ 2) = U.indicator 1 := by
      funext x
      by_cases hx : x ∈ U
      · simp [hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hpt, MeasureTheory.lintegral_indicator_one hU_meas]
  rw [← h_lintegral_m, ← h_lintegral_msq, ← h_integral_U]
  exact h_eq_indicator ▸ hCS_lintegral

end

end
