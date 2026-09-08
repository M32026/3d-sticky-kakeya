/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.EDPacking.IntersectionVolume
public import Kakeya.ConvexBody

/-!
# Axial angle bound for bad-density tubes

If a δ-tube satisfies the bad-density condition against a reference tube, then
its direction makes a small angle with the reference direction.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped InnerProductSpace RealInnerProductSpace
open Kakeya.Tube

namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-! ### Bad-density ⟹ axial-angle constraint

First step of the direction-count argument for `badAgainstSet_card_le_M2_cN` in
`Kakeya/Tube/EDPacking/BadCount.lean`.

If `T_i : Tube δ E` satisfies the bad-density condition
`c · vol(T_i.carrier) ≤ vol(T_i.carrier ∩ cthickening (99·δ) T₀'.carrier)`,
then the projective direction-distance of `T_i.direction` from
`T₀'.direction` is `≤ C · δ / c` for a uniform dimension-only
constant `C > 0`.

**Geometric picture.** The cthickened tube `K = cthickening (99·δ) T₀'.carrier`
has length `1 + 200·δ` along `T₀'.direction` and radius `100·δ` perpendicular.
A line in direction `e` intersects `K` in a chord of length
`≲ 200·δ / max(sin∠(e, T₀'.direction), 100·δ)`. Combined with the bad-density
hypothesis (via Fubini), this forces `sin∠ ≲ δ / c`, hence the projective
distance bound. The Fubini chord bound on `vol(T_i ∩ K)` is supplied by
`Tube.vol_inter_carrier_cthickening_le`. -/

/-- **Bad ⟹ small axial angle.**

If `T_i : Tube δ E` satisfies the bad-density condition
`c · vol(T_i.carrier) ≤ vol(T_i.carrier ∩ cthickening (99·δ) T₀'.carrier)`,
then the projective angular distance from `T_i.direction` to
`T₀'.direction` is `≤ C · δ / c` for a uniform dimension-only constant
`C > 0`:
```
min ‖T_i.direction - T₀'.direction‖ ‖T_i.direction + T₀'.direction‖ ≤ C(n) · δ / c.
```

This is the angular containment statement consumed by the cap-subdivision
step of `badAgainstSet_card_le_M2_cN`. -/
lemma bad_axial_angle_le
    (hn : 1 < Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : δ ≤ 1) (T_i T₀' : Tube δ E)
        {c : ℝ} (_hc : 0 < c) (_hc_le : c ≤ 1)
        (_h_bad : ENNReal.ofReal c * volume T_i.carrier
            ≤ volume (T_i.carrier ∩
                Metric.cthickening (99 * δ) T₀'.carrier)),
        min ‖T_i.direction - T₀'.direction‖
            ‖T_i.direction + T₀'.direction‖ ≤ C * δ / c := by
  have hn_pos : 0 < Module.finrank ℝ E := by omega
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) hn_pos
  set C₃ : ℝ := intersectionVolumeConstant E with hC₃_def
  have hC₃_pos : 0 < C₃ := by
    rw [hC₃_def]
    exact intersectionVolumeConstant_pos E
  set c' : ℝ := (Tube.le_volume.c (Module.finrank ℝ E) : ℝ) with hc'_def
  have hc'_pos : 0 < c' := by
    rw [hc'_def]; exact NNReal.coe_pos.mpr (Tube.le_volume.c_pos _)
  have hc'_bound : ∀ (δ : NNReal), 0 < δ → ∀ T : Tube δ E,
      c' * (δ : ℝ) ^ (Module.finrank ℝ E - 1) ≤ volume.real T.carrier := by
    intro δ _ T
    have h := Tube.le_volume (δ := δ) T
    have hreal := ENNReal.toReal_mono T.isCompact.measure_lt_top.ne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hreal
    exact hreal
  refine ⟨C₃ / c', div_pos hC₃_pos hc'_pos, ?_⟩
  intro δ hδ hδ_le T_i T₀' c hc hc_le h_bad
  have h_inter_fin :
      volume (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top T_i.isCompact.measure_lt_top.ne
      (measure_mono Set.inter_subset_left)
  have h_bad_real := ENNReal.toReal_mono h_inter_fin h_bad
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at h_bad_real
  set n : ℕ := Module.finrank ℝ E with hn_def
  set u : E := T_i.direction with hu_def
  set v : E := T₀'.direction with hv_def
  set θ_sub : ℝ := ‖u - v‖ with hθ_sub_def
  set θ_add : ℝ := ‖u + v‖ with hθ_add_def
  have hn_ge_one : 1 ≤ n := hn_pos
  have hn_succ : n = (n - 1) + 1 := by omega
  have hδ_pow : ((δ : ℝ) ^ n : ℝ) = (δ : ℝ) ^ (n - 1) * (δ : ℝ) := by
    conv_lhs => rw [hn_succ]
    rw [pow_succ]
  have hδ_pow_pos : 0 < δ ^ (n - 1) := pow_pos hδ _
  by_cases h_case : θ_sub ≤ θ_add
  · have h_min_eq : min θ_sub θ_add = θ_sub := min_eq_left h_case
    rw [h_min_eq]
    by_cases h_zero : θ_sub = 0
    · rw [h_zero]
      apply div_nonneg
      · apply mul_nonneg
        · exact (div_pos hC₃_pos hc'_pos).le
        · exact hδ.le
      · exact hc.le
    · have hθ_sub_pos : 0 < θ_sub := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
      have hθ_sub_alt : ‖v - u‖ = θ_sub := by
        rw [hθ_sub_def, ← neg_sub u v, norm_neg]
      have hθ_add_alt : ‖v + u‖ = θ_add := by
        rw [hθ_add_def, add_comm]
      have h_dir_min' : ‖v - u‖ ≤ ‖v + u‖ := by
        rw [hθ_sub_alt, hθ_add_alt]; exact h_case
      have hv_sub_u_pos : 0 < ‖v - u‖ := by rw [hθ_sub_alt]; exact hθ_sub_pos
      have h_helper := vol_inter_carrier_cthickening_le
        (E := E) hδ hδ_le T_i T₀' h_dir_min' hv_sub_u_pos
      rw [hθ_sub_alt] at h_helper
      have h_helper_real :
          volume.real (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
            C₃ * δ ^ n / θ_sub := by
        have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_helper
        rw [ENNReal.toReal_ofReal] at hreal
        · simpa [Measure.real, hC₃_def, hn_def] using hreal
        · positivity
      have h_vol_lb : c' * δ ^ (n - 1) ≤ volume.real T_i.carrier := hc'_bound δ hδ T_i
      have h_chain1 : c * (c' * δ ^ (n - 1)) ≤ c * volume.real T_i.carrier :=
        mul_le_mul_of_nonneg_left h_vol_lb hc.le
      have h_chain2 : c * volume.real T_i.carrier ≤ C₃ * δ ^ n / θ_sub :=
        h_bad_real.trans h_helper_real
      have h_chain : c * (c' * δ ^ (n - 1)) ≤ C₃ * δ ^ n / θ_sub :=
        h_chain1.trans h_chain2
      have h_cc' : 0 < c * (c' * δ ^ (n - 1)) := by positivity
      have h_div : θ_sub ≤ C₃ * δ ^ n / (c * (c' * δ ^ (n - 1))) := by
        rw [le_div_iff₀ h_cc']
        have := (le_div_iff₀ hθ_sub_pos).mp h_chain
        linarith
      have h_simp : C₃ * δ ^ n / (c * (c' * δ ^ (n - 1))) = C₃ / c' * δ / c := by
        rw [hδ_pow]
        field_simp
      rw [h_simp] at h_div
      exact h_div
  · push Not at h_case
    have h_add_le_sub : θ_add ≤ θ_sub := h_case.le
    have h_min_eq : min θ_sub θ_add = θ_add := min_eq_right h_add_le_sub
    rw [h_min_eq]
    by_cases h_zero : θ_add = 0
    · rw [h_zero]
      apply div_nonneg
      · apply mul_nonneg
        · exact (div_pos hC₃_pos hc'_pos).le
        · exact hδ.le
      · exact hc.le
    · have hθ_add_pos : 0 < θ_add := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero)
      set T_i' : Tube δ E := T_i.reverse with hT_i'_def
      have hT_i'_dir : T_i'.direction = -u := by
        rw [hT_i'_def, Tube.reverse_direction, hu_def]
      have hT_i'_carrier : T_i'.carrier = T_i.carrier := by
        rw [hT_i'_def]; rfl
      have h_norm_sub_rev : ‖v - T_i'.direction‖ = θ_add := by
        rw [hT_i'_dir, sub_neg_eq_add, hθ_add_def, add_comm]
      have h_norm_add_rev : ‖v + T_i'.direction‖ = θ_sub := by
        rw [hT_i'_dir, ← sub_eq_add_neg, hθ_sub_def, ← neg_sub u v, norm_neg]
      have h_dir_min' : ‖v - T_i'.direction‖ ≤ ‖v + T_i'.direction‖ := by
        rw [h_norm_sub_rev, h_norm_add_rev]; exact h_add_le_sub
      have hv_sub_pos : 0 < ‖v - T_i'.direction‖ := by
        rw [h_norm_sub_rev]; exact hθ_add_pos
      have h_helper := vol_inter_carrier_cthickening_le
        (E := E) hδ hδ_le T_i' T₀' h_dir_min' hv_sub_pos
      rw [hT_i'_carrier] at h_helper
      rw [h_norm_sub_rev] at h_helper
      have h_helper_real :
          volume.real (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
            C₃ * δ ^ n / θ_add := by
        have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_helper
        rw [ENNReal.toReal_ofReal] at hreal
        · simpa [Measure.real, hC₃_def, hn_def] using hreal
        · positivity
      have h_vol_lb : c' * δ ^ (n - 1) ≤ volume.real T_i.carrier := hc'_bound δ hδ T_i
      have h_chain1 : c * (c' * δ ^ (n - 1)) ≤ c * volume.real T_i.carrier :=
        mul_le_mul_of_nonneg_left h_vol_lb hc.le
      have h_chain2 : c * volume.real T_i.carrier ≤ C₃ * δ ^ n / θ_add :=
        h_bad_real.trans h_helper_real
      have h_chain : c * (c' * δ ^ (n - 1)) ≤ C₃ * δ ^ n / θ_add :=
        h_chain1.trans h_chain2
      have h_cc' : 0 < c * (c' * δ ^ (n - 1)) := by positivity
      have h_div : θ_add ≤ C₃ * δ ^ n / (c * (c' * δ ^ (n - 1))) := by
        rw [le_div_iff₀ h_cc']
        have := (le_div_iff₀ hθ_add_pos).mp h_chain
        linarith
      have h_simp : C₃ * δ ^ n / (c * (c' * δ ^ (n - 1))) = C₃ / c' * δ / c := by
        rw [hδ_pow]
        field_simp
      rw [h_simp] at h_div
      exact h_div

end -- close noncomputable section
end Kakeya
