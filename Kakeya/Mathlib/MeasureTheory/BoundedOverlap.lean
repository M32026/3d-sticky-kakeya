/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Bounded-overlap union estimate

If a finite family of measurable sets `A i` has *bounded overlap* — every point
belongs to at most `C` of them — then the sum of their measures is at most `C`
times the measure of their union.

This is the abstract measure-theoretic content behind the bounded-overlap step in
the plank-to-tube reduction (GWZ Lemma 6.13, item 3): the slab subfamilies
`U(𝒫'_S, Y'_S)` overlap boundedly, so `∑_S |U(𝒫'_S, Y'_S)| ≤ C |U(𝒫', Y')|`.
-/

@[expose] public section

open MeasureTheory ENNReal

namespace MeasureTheory

variable {α ι : Type*} {m : MeasurableSpace α} {μ : Measure α}

open Classical in
/-- **Bounded-overlap union estimate.** Let `A : ι → Set α` be a finite family of
measurable sets indexed by `s`, and suppose every point lies in at most `C` of them
(`{i ∈ s | x ∈ A i}.card ≤ C` for all `x`). Then
`∑ i ∈ s, μ (A i) ≤ C * μ (⋃ i ∈ s, A i)`.

The proof writes each measure as the Lebesgue integral of an indicator, swaps sum
and integral, and bounds the pointwise overlap count `∑ i, 𝟙_{A i}(x)` by
`C · 𝟙_{⋃ A i}(x)`. -/
theorem sum_measure_le_mul_measure_biUnion_of_card_filter_le
    (s : Finset ι) {A : ι → Set α} (hA : ∀ i ∈ s, MeasurableSet (A i)) {C : ℕ}
    (hC : ∀ x, {i ∈ s | x ∈ A i}.card ≤ C) :
    ∑ i ∈ s, μ (A i) ≤ (C : ℝ≥0∞) * μ (⋃ i ∈ s, A i) := by
  have hUnion : MeasurableSet (⋃ i ∈ s, A i) := Finset.measurableSet_biUnion s hA
  have hmeas : ∀ i ∈ s, Measurable (fun x => (A i).indicator (1 : α → ℝ≥0∞) x) :=
    fun i hi => measurable_const.indicator (hA i hi)
  have hUmeas : Measurable (fun x => (⋃ i ∈ s, A i).indicator (1 : α → ℝ≥0∞) x) :=
    measurable_const.indicator hUnion
  have hsum : ∑ i ∈ s, μ (A i) = ∫⁻ x, ∑ i ∈ s, (A i).indicator 1 x ∂μ := by
    rw [lintegral_finsetSum s hmeas]
    exact Finset.sum_congr rfl (fun i hi => (lintegral_indicator_one (hA i hi)).symm)
  rw [hsum]
  calc ∫⁻ x, ∑ i ∈ s, (A i).indicator 1 x ∂μ
      ≤ ∫⁻ x, (C : ℝ≥0∞) * (⋃ i ∈ s, A i).indicator 1 x ∂μ := by
        refine lintegral_mono (fun x => ?_)
        change ∑ i ∈ s, (A i).indicator (1 : α → ℝ≥0∞) x
            ≤ (C : ℝ≥0∞) * (⋃ i ∈ s, A i).indicator 1 x
        have hpt : ∑ i ∈ s, (A i).indicator (1 : α → ℝ≥0∞) x
            = (({i ∈ s | x ∈ A i}).card : ℝ≥0∞) := by
          simp only [Set.indicator_apply, Pi.one_apply]
          exact Finset.sum_boole (fun i => x ∈ A i) s
        rw [hpt]
        by_cases hx : x ∈ ⋃ i ∈ s, A i
        · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
          exact Nat.cast_le.mpr (hC x)
        · rw [Set.indicator_of_notMem hx, mul_zero]
          have he : {i ∈ s | x ∈ A i} = (∅ : Finset ι) :=
            Finset.filter_eq_empty_iff.mpr
              (fun i hi hmem => hx (Set.mem_biUnion hi hmem))
          simp [he]
    _ = (C : ℝ≥0∞) * μ (⋃ i ∈ s, A i) := by
        rw [lintegral_const_mul _ hUmeas, lintegral_indicator_one hUnion]

open Classical in
/-- **Measurability of the overlap count.**  For a finite family of measurable sets the
`ℝ≥0∞`-valued counting function `x ↦ #{i ∈ s | x ∈ A i}` is measurable, being a finite sum of
indicators. -/
theorem measurable_card_filter_mem (s : Finset ι) {A : ι → Set α}
    (hA : ∀ i ∈ s, MeasurableSet (A i)) :
    Measurable (fun x => (({i ∈ s | x ∈ A i}).card : ℝ≥0∞)) := by
  have hmeas : ∀ i ∈ s, Measurable (fun x : α => (A i).indicator (1 : α → ℝ≥0∞) x) :=
    fun i hi => measurable_const.indicator (hA i hi)
  have hsum_meas : Measurable (fun x : α => ∑ i ∈ s, (A i).indicator (1 : α → ℝ≥0∞) x) :=
    Finset.measurable_fun_sum s hmeas
  simpa [Set.indicator_apply, Pi.one_apply, Finset.sum_boole] using hsum_meas

open Classical in
/-- **Layer cake for a finite family of sets.**  For a finite family of measurable sets `A i`,
`i ∈ s`, and an arbitrary set `B`, the total mass of the family inside `B` is the integral over
`B` of the overlap count:
`∑ i ∈ s, μ (A i ∩ B) = ∫⁻ x in B, #{i ∈ s | x ∈ A i} ∂μ`.

No measurability is required of `B`: the identity is Fubini for a finite sum of indicators against
the restricted measure `μ.restrict B`, and `Measure.restrict_apply` only needs the sets `A i` to be
measurable.  This is the linear companion of
`MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le`; the latter is the special
case where the count is bounded by a constant.

The set-integral form is what distinguishes this from
`MeasureTheory.sum_measure_inter_eq_lintegral_card_filter`, which fixes the intersected set and
indexes the other factor. -/
theorem sum_measure_inter_eq_setLIntegral_card_filter
    (s : Finset ι) {A : ι → Set α} (hA : ∀ i ∈ s, MeasurableSet (A i)) (B : Set α) :
    ∑ i ∈ s, μ (A i ∩ B) = ∫⁻ x in B, (({i ∈ s | x ∈ A i}).card : ℝ≥0∞) ∂μ := by
  -- The integrals over B are integrals against μ.restrict B
  calc
    ∑ i ∈ s, μ (A i ∩ B)
        = ∑ i ∈ s, (μ.restrict B) (A i) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          rw [Measure.restrict_apply (hA i hi)]
    _ = ∑ i ∈ s, ∫⁻ x, (A i).indicator 1 x ∂(μ.restrict B) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [lintegral_indicator_one (hA i hi)]
    _ = ∫⁻ x, ∑ i ∈ s, (A i).indicator 1 x ∂(μ.restrict B) := by
      have hmeas_restr : ∀ i ∈ s, Measurable (fun x : α => (A i).indicator (1 : α → ℝ≥0∞) x) :=
        fun i hi => measurable_const.indicator (hA i hi)
      rw [lintegral_finsetSum s hmeas_restr]
    _ = ∫⁻ x in B, ∑ i ∈ s, (A i).indicator 1 x ∂μ := rfl
    _ = ∫⁻ x in B, (({i ∈ s | x ∈ A i}).card : ℝ≥0∞) ∂μ := by
      refine lintegral_congr (fun x => ?_)
      simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole]

open Classical in
/-- Volume-specialized compatibility form of the bounded-overlap estimate. -/
lemma sum_volume_le_mul_volume_biUnion
    {F : Type*} [MeasureSpace F]
    {s : Finset ι} {A : ι → Set F} {C : ℕ}
    (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hC : ∀ x, {i ∈ s | x ∈ A i}.card ≤ C) :
    ∑ i ∈ s, volume (A i) ≤ (C : ENNReal) * volume (⋃ i ∈ s, A i) :=
  sum_measure_le_mul_measure_biUnion_of_card_filter_le s hmeas hC

end MeasureTheory
