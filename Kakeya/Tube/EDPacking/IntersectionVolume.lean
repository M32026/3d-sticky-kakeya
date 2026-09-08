/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexBody
public import Kakeya.Tube.CylinderApprox
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Tube intersection-volume bounds for ED packing

Geometric bounds for the volume of a tube intersected with the closed thickening
of another tube, in terms of the angle between their directions. These estimates
feed the direction-packing argument in `Kakeya.Tube.EDPacking.BadCount`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped InnerProductSpace RealInnerProductSpace

namespace Kakeya.Tube

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

universe u

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Helper 1 (cthickening as bigger cylinder).** For any tube `T : Tube δ E`
with `0 ≤ δ` and any `r ≥ 0`, the closed `r`-thickening of `T.carrier` is
contained in the axis cylinder centred at `T.midpoint`, along `T.direction`,
of half-length `1/2 + (δ + r)` and cross-section radius `δ + r`.

Proof sketch: `T.carrier` is the union of closed `δ`-balls around points of
the segment `[T.x, T.y]`, and is `IsCompact`. For `p ∈ cthickening r T.carrier`
there is some `q ∈ T.carrier` with `dist p q ≤ r`. Writing `q ∈ closedBall z δ`
for `z` on the segment gives `dist p z ≤ δ + r`. Then the same algebra as
`carrier_subset_cylinder_self`, with `δ` replaced by `δ + r`, yields the
cylinder containment. -/
lemma cthickening_carrier_subset_cylinder
    {δ : NNReal} (T : Tube δ E) {r : ℝ} (hr : 0 ≤ r) :
    Metric.cthickening r T.carrier ⊆
      cylinder T.midpoint T.direction
        (-(1 / 2) - ((δ : ℝ) + r)) (1 / 2 + ((δ : ℝ) + r)) ((δ : ℝ) + r) := by
  have hδ : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
  have hδr : (0 : ℝ) ≤ (δ : ℝ) + r := add_nonneg hδ hr
  have hu_norm : ‖T.direction‖ = 1 := by
    have := T.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have h_inner_u_u : (inner ℝ T.direction T.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hu_norm]; ring
  have hx_mem : T.x ∈ T.carrier := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y, ?_⟩
    exact Metric.mem_closedBall_self hδ
  have hT_nonempty : T.carrier.Nonempty := ⟨T.x, hx_mem⟩
  have hT_compact : IsCompact T.carrier := T.isCompact
  intro p hp
  rw [Metric.mem_cthickening_iff] at hp
  have h_infDist_le : Metric.infDist p T.carrier ≤ r := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
    rw [ENNReal.toReal_ofReal hr] at h
    exact h
  obtain ⟨q, hq_mem, hpq_eq⟩ := hT_compact.exists_infDist_eq_dist hT_nonempty p
  have hpq_le : dist p q ≤ r := by rw [← hpq_eq]; exact h_infDist_le
  rw [T.carrier_eq] at hq_mem
  obtain ⟨z, hz_seg, hqz⟩ := Set.mem_iUnion₂.mp hq_mem
  obtain ⟨α, β, hα, hβ, hαβ, hz_eq⟩ := hz_seg
  set s : ℝ := β - 1 / 2 with hs_def
  have hs_lb : -(1 / 2 : ℝ) ≤ s := by linarith
  have hs_ub : s ≤ 1 / 2 := by linarith
  have hz_alt : z = T.midpoint + s • T.direction := by
    rw [← hz_eq]
    change α • T.x + β • T.y = (1/2 : ℝ) • (T.x + T.y) + s • (T.y - T.x)
    simp only [hs_def, smul_add, smul_sub]
    have hα_eq : α = 1 - β := by linarith
    rw [hα_eq, sub_smul, one_smul]
    module
  have hpz_norm : ‖p - z‖ ≤ δ + r := by
    have hqz_norm : ‖q - z‖ ≤ δ := by
      rw [← dist_eq_norm]; exact hqz
    have hpq_norm : ‖p - q‖ ≤ r := by
      rw [← dist_eq_norm]; exact hpq_le
    calc ‖p - z‖ = ‖(p - q) + (q - z)‖ := by congr 1; abel
      _ ≤ ‖p - q‖ + ‖q - z‖ := norm_add_le _ _
      _ ≤ r + δ := add_le_add hpq_norm hqz_norm
      _ = δ + r := by ring
  set θ : ℝ := (inner ℝ (p - T.midpoint) T.direction : ℝ) with hθ_def
  have h_inner_pz : (inner ℝ (p - z) T.direction : ℝ) = θ - s := by
    rw [hz_alt]
    have : p - (T.midpoint + s • T.direction) = (p - T.midpoint) - s • T.direction := by abel
    rw [this, inner_sub_left, inner_smul_left, h_inner_u_u, RCLike.conj_to_real, mul_one]
  have h_inner_pz_abs : |θ - s| ≤ δ + r := by
    have h_abs_le : |(inner ℝ (p - z) T.direction : ℝ)| ≤ ‖p - z‖ * ‖T.direction‖ :=
      abs_real_inner_le_norm _ _
    rw [hu_norm, mul_one] at h_abs_le
    rw [h_inner_pz] at h_abs_le
    exact h_abs_le.trans hpz_norm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h1 : -(δ + r) ≤ θ - s := (abs_le.mp h_inner_pz_abs).1
    linarith
  · have h2 : θ - s ≤ δ + r := (abs_le.mp h_inner_pz_abs).2
    linarith
  · have h_split : (p - T.midpoint) - θ • T.direction =
        (p - z) - (θ - s) • T.direction := by
      rw [hz_alt, sub_smul]; module
    rw [h_split]
    have h_inner_zero :
        (inner ℝ ((p - z) - (θ - s) • T.direction) T.direction : ℝ) = 0 := by
      rw [inner_sub_left, inner_smul_left, h_inner_u_u, RCLike.conj_to_real, mul_one]
      rw [h_inner_pz]; ring
    have h_norm_sq : ‖(p - z) - (θ - s) • T.direction‖ ^ 2 =
        ‖p - z‖ ^ 2 - (θ - s) ^ 2 := by
      have h1 : ‖(p - z) - (θ - s) • T.direction‖ ^ 2 =
          ‖p - z‖ ^ 2 - 2 * (θ - s) * (inner ℝ (p - z) T.direction : ℝ)
            + (θ - s) ^ 2 * ‖T.direction‖ ^ 2 := by
        rw [@norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
            inner_smul_right, sq_abs]
        ring
      rw [h1, hu_norm, h_inner_pz]
      ring
    have h_sq_le : ‖(p - z) - (θ - s) • T.direction‖ ^ 2 ≤ (δ + r) ^ 2 := by
      rw [h_norm_sq]
      have hpz_sq : ‖p - z‖ ^ 2 ≤ (δ + r) ^ 2 := by
        have hnn : 0 ≤ ‖p - z‖ := norm_nonneg _
        nlinarith [hpz_norm]
      nlinarith [sq_nonneg (θ - s)]
    have hnn1 : 0 ≤ ‖(p - z) - (θ - s) • T.direction‖ := norm_nonneg _
    have := abs_le_of_sq_le_sq h_sq_le hδr
    rwa [abs_of_nonneg hnn1] at this

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Helper 2 (axis-parameter bound through cthickened tube).** Mirror of
`Tube.exists_axis_param_bound`, where the first tube
`T₀'` is replaced by its closed `r`-thickening. For any
`p ∈ cthickening r T₀'.carrier ∩ T_i.carrier`, the axis parameter of `p` along
`T_i.direction` is within `δ + √2·(2δ + r)/θ` of a single `s_star`, where
`θ = ‖T₀'.direction - T_i.direction‖`. -/
lemma exists_axis_param_bound_thick
    {δ : NNReal} (hδ_pos : 0 < δ) {r : ℝ} (hr : 0 ≤ r) (T₀' T_i : Tube δ E)
    (h_dir_min :
      ‖T₀'.direction - T_i.direction‖ ≤ ‖T₀'.direction + T_i.direction‖)
    (h_θ_pos : 0 < ‖T₀'.direction - T_i.direction‖) :
    ∃ s_star : ℝ, ∀ p ∈ Metric.cthickening r T₀'.carrier ∩ T_i.carrier,
      |(inner ℝ (p - T_i.midpoint) T_i.direction : ℝ) - s_star| ≤
        (δ : ℝ) + Real.sqrt 2 * (2 * (δ : ℝ) + r) / ‖T₀'.direction - T_i.direction‖ := by
  have hδr_pos : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ_pos
  have hδr_nn : (0 : ℝ) ≤ (δ : ℝ) := hδr_pos.le
  set u : E := T_i.direction with hu_def
  set v : E := T₀'.direction with hv_def
  have hu_norm : ‖u‖ = 1 := by
    have := T_i.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have hv_norm : ‖v‖ = 1 := by
    have := T₀'.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have h_inner_uu : (inner ℝ u u : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hu_norm]; ring
  have h_inner_vv : (inner ℝ v v : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv_norm]; ring
  set θ : ℝ := ‖v - u‖ with hθ_def
  have hθ_pos : 0 < θ := h_θ_pos
  set c : ℝ := (inner ℝ u v : ℝ) with hc_def
  have h_inner_vu : (inner ℝ v u : ℝ) = c := by
    rw [hc_def, real_inner_comm]
  have hθ_sq : θ ^ 2 = 2 - 2 * c := by
    have := @norm_sub_sq_real _ _ _ v u
    rw [hv_norm, hu_norm, h_inner_vu] at this
    linarith [this, hθ_def]
  have h_add_sq : ‖v + u‖ ^ 2 = 2 + 2 * c := by
    have := @norm_add_sq_real _ _ _ v u
    rw [hv_norm, hu_norm, h_inner_vu] at this
    linarith
  have hc_eq : c = 1 - θ ^ 2 / 2 := by linarith
  have hc_nn : 0 ≤ c := by
    have h_dir_min' : θ ≤ ‖v + u‖ := h_dir_min
    have hθ_nn : 0 ≤ θ := norm_nonneg _
    have h_sq : θ ^ 2 ≤ ‖v + u‖ ^ 2 := by
      have h_norm_add_nn : 0 ≤ ‖v + u‖ := norm_nonneg _
      nlinarith [h_dir_min', hθ_nn, h_norm_add_nn]
    rw [h_add_sq] at h_sq
    linarith [hθ_sq]
  have hθ_sq_le_two : θ ^ 2 ≤ 2 := by linarith
  have h_one_minus_c_sq : θ ^ 2 / 2 ≤ 1 - c ^ 2 := by
    have hθ_sq_nn : 0 ≤ θ ^ 2 := sq_nonneg _
    nlinarith [hc_eq, sq_nonneg θ, hθ_sq_le_two, hθ_sq_nn]
  have h_one_minus_c_sq_pos : 0 < 1 - c ^ 2 :=
    lt_of_lt_of_le (by positivity) h_one_minus_c_sq
  set A : E := T_i.midpoint - T₀'.midpoint with hA_def
  set Au : ℝ := (inner ℝ A u : ℝ) with hAu_def
  set Av : ℝ := (inner ℝ A v : ℝ) with hAv_def
  set s_star : ℝ := -(Au - c * Av) / (1 - c ^ 2) with hs_star_def
  refine ⟨s_star, ?_⟩
  rintro p ⟨hp1, hp2⟩
  have hp1_cyl : p ∈ cylinder T₀'.midpoint v
      (-(1 / 2) - ((δ : ℝ) + r)) (1 / 2 + ((δ : ℝ) + r)) ((δ : ℝ) + r) :=
    cthickening_carrier_subset_cylinder T₀' hr hp1
  rw [mem_cylinder] at hp1_cyl
  set s₁ : ℝ := (inner ℝ (p - T₀'.midpoint) v : ℝ) with hs₁_def
  have hp_T1_norm : ‖(p - T₀'.midpoint) - s₁ • v‖ ≤ (δ : ℝ) + r := hp1_cyl.2
  set δR : ℝ := (δ : ℝ) with hδR_def
  rw [T_i.carrier_eq] at hp2
  obtain ⟨z₂, hz₂_seg, hpz₂⟩ := Set.mem_iUnion₂.mp hp2
  obtain ⟨α₂, β₂, hα₂, hβ₂, hαβ₂, hz₂_eq⟩ := hz₂_seg
  set s₂ : ℝ := β₂ - 1 / 2 with hs₂_def
  have hs₂_lb : -(1 / 2 : ℝ) ≤ s₂ := by linarith
  have hs₂_ub : s₂ ≤ 1 / 2 := by linarith
  have hz₂_alt : z₂ = T_i.midpoint + s₂ • u := by
    rw [← hz₂_eq]
    change α₂ • T_i.x + β₂ • T_i.y = (1/2 : ℝ) • (T_i.x + T_i.y) + s₂ • (T_i.y - T_i.x)
    simp only [hs₂_def, smul_add, smul_sub]
    have hα₂_eq : α₂ = 1 - β₂ := by linarith
    rw [hα₂_eq, sub_smul, one_smul]
    module
  have hpz₂_norm : ‖p - z₂‖ ≤ δ := by rw [← dist_eq_norm]; exact hpz₂
  have hp_T2_norm : ‖p - T_i.midpoint - s₂ • u‖ ≤ δ := by
    have heq : p - T_i.midpoint - s₂ • u = p - z₂ := by
      rw [hz₂_alt]; abel
    rw [heq]; exact hpz₂_norm
  set B : E := A + s₂ • u - s₁ • v with hB_def
  have hB_id : B = -(p - T_i.midpoint - s₂ • u) + ((p - T₀'.midpoint) - s₁ • v) := by
    simp only [hB_def, hA_def]; abel
  have hB_norm : ‖B‖ ≤ 2 * δ + r := by
    rw [hB_id]
    calc ‖-(p - T_i.midpoint - s₂ • u) + ((p - T₀'.midpoint) - s₁ • v)‖
        ≤ ‖-(p - T_i.midpoint - s₂ • u)‖ + ‖(p - T₀'.midpoint) - s₁ • v‖ :=
          norm_add_le _ _
      _ = ‖p - T_i.midpoint - s₂ • u‖ + ‖(p - T₀'.midpoint) - s₁ • v‖ := by
          rw [norm_neg]
      _ ≤ δ + (δ + r) := add_le_add hp_T2_norm hp_T1_norm
      _ = 2 * δ + r := by ring
  have h_2δr_nn : 0 ≤ 2 * δ + r := by linarith [hδ_pos.le, hr]
  have hB_norm_sq : ‖B‖ ^ 2 ≤ (2 * δ + r) ^ 2 := by
    have hnn : 0 ≤ ‖B‖ := norm_nonneg _
    nlinarith [hB_norm, h_2δr_nn]
  have h_inner_Bv : (inner ℝ B v : ℝ) = Av + s₂ * c - s₁ := by
    simp only [hB_def]
    rw [inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
        h_inner_vv, hc_def, RCLike.conj_to_real, RCLike.conj_to_real]
    change Av + s₂ * c - s₁ * 1 = Av + s₂ * c - s₁
    ring
  set Bv : ℝ := (inner ℝ B v : ℝ) with hBv_def
  have h_B_perp_v : (inner ℝ (B - Bv • v) v : ℝ) = 0 := by
    rw [inner_sub_left, inner_smul_left, h_inner_vv, RCLike.conj_to_real, mul_one]
    change Bv - Bv = 0; ring
  have h_perp_norm_sq : ‖B - Bv • v‖ ^ 2 = ‖B‖ ^ 2 - Bv ^ 2 := by
    have h1 : ‖B - Bv • v‖ ^ 2 =
        ‖B‖ ^ 2 - 2 * (inner ℝ B (Bv • v) : ℝ) + ‖Bv • v‖ ^ 2 := by
      rw [@norm_sub_sq_real]
    rw [h1]
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv_norm]
    change ‖B‖ ^ 2 - 2 * (Bv * Bv) + (Bv ^ 2 * 1 ^ 2) = ‖B‖ ^ 2 - Bv ^ 2
    ring
  set A_perp : E := A - Av • v with hAperp_def
  set u_perp : E := u - c • v with huperp_def
  have h_B_perp_eq : B - Bv • v = A_perp + s₂ • u_perp := by
    have hBv_val : Bv = Av + s₂ * c - s₁ := h_inner_Bv
    have hgoal : B - Bv • v = (A - Av • v) + s₂ • (u - c • v) := by
      have h1 : B = A + s₂ • u - s₁ • v := hB_def
      have h2 : Bv • v = (Av + s₂ * c - s₁) • v := by rw [hBv_val]
      have h3 : (Av + s₂ * c - s₁ : ℝ) • v
            = Av • v + s₂ • (c • v) - s₁ • v := by
        rw [sub_smul, add_smul, mul_smul]
      have h4 : s₂ • (u - c • v) = s₂ • u - s₂ • (c • v) := smul_sub _ _ _
      rw [h1, h2, h3, h4]
      abel
    rw [hgoal, hAperp_def, huperp_def]
  have h_inner_Aperp_v : (inner ℝ A_perp v : ℝ) = 0 := by
    rw [hAperp_def, inner_sub_left, inner_smul_left, h_inner_vv,
        RCLike.conj_to_real, mul_one]
    change Av - Av = 0; ring
  have h_uperp_norm_sq : ‖u_perp‖ ^ 2 = 1 - c ^ 2 := by
    have : ‖u_perp‖ ^ 2 = ‖u‖ ^ 2 - 2 * (inner ℝ u (c • v) : ℝ) + ‖c • v‖ ^ 2 := by
      rw [huperp_def, @norm_sub_sq_real]
    rw [this, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu_norm, hv_norm]
    change (1 : ℝ) ^ 2 - 2 * (c * c) + c ^ 2 * 1 ^ 2 = 1 - c ^ 2
    ring
  have h_inner_Aperp_uperp : (inner ℝ A_perp u_perp : ℝ) = Au - c * Av := by
    have h_step1 : (inner ℝ A_perp u_perp : ℝ) =
        (inner ℝ A_perp u : ℝ) - c * (inner ℝ A_perp v : ℝ) := by
      rw [huperp_def, inner_sub_right, inner_smul_right]
    have h_step2 : (inner ℝ A_perp u : ℝ) = Au - Av * c := by
      have hsub : (inner ℝ A_perp u : ℝ) =
          (inner ℝ A u : ℝ) - Av * (inner ℝ v u : ℝ) := by
        rw [hAperp_def, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
      rw [hsub, h_inner_vu]
    rw [h_step1, h_step2, h_inner_Aperp_v]
    ring
  have h_norm_perp_eq : ‖A_perp + s₂ • u_perp‖ ^ 2 =
      ‖A_perp‖ ^ 2 + 2 * s₂ * (Au - c * Av) + s₂ ^ 2 * (1 - c ^ 2) := by
    have h1 : ‖A_perp + s₂ • u_perp‖ ^ 2 =
        ‖A_perp‖ ^ 2 + 2 * (inner ℝ A_perp (s₂ • u_perp) : ℝ) + ‖s₂ • u_perp‖ ^ 2 := by
      rw [@norm_add_sq_real]
    rw [h1, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        h_inner_Aperp_uperp, h_uperp_norm_sq]
    ring
  have h_CS : (Au - c * Av) ^ 2 ≤ ‖A_perp‖ ^ 2 * (1 - c ^ 2) := by
    have h1 : |(inner ℝ A_perp u_perp : ℝ)| ≤ ‖A_perp‖ * ‖u_perp‖ :=
      abs_real_inner_le_norm _ _
    rw [h_inner_Aperp_uperp] at h1
    have h2 : (Au - c * Av) ^ 2 ≤ (‖A_perp‖ * ‖u_perp‖) ^ 2 := by
      have h_abs_nn : 0 ≤ |Au - c * Av| := abs_nonneg _
      have h_rhs_nn : 0 ≤ ‖A_perp‖ * ‖u_perp‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      have : |Au - c * Av| ^ 2 ≤ (‖A_perp‖ * ‖u_perp‖) ^ 2 := by
        rw [sq, sq]; exact mul_le_mul h1 h1 h_abs_nn h_rhs_nn
      rwa [sq_abs] at this
    rw [mul_pow, h_uperp_norm_sq] at h2
    exact h2
  have h_completing_sq : (1 - c ^ 2) * (s₂ - s_star) ^ 2 ≤ ‖A_perp + s₂ • u_perp‖ ^ 2 := by
    rw [h_norm_perp_eq]
    have h_ne : (1 - c ^ 2) ≠ 0 := ne_of_gt h_one_minus_c_sq_pos
    have h_star_eq : (1 - c ^ 2) * s_star = -(Au - c * Av) := by
      rw [hs_star_def, mul_div_assoc']
      rw [mul_comm (1 - c ^ 2) _]
      rw [mul_div_assoc, div_self h_ne, mul_one]
    have h_star_sq : (1 - c ^ 2) * s_star ^ 2 = (Au - c * Av) ^ 2 / (1 - c ^ 2) := by
      have hcalc : (1 - c ^ 2) * s_star ^ 2 = ((1 - c ^ 2) * s_star) * s_star := by ring
      rw [hcalc, h_star_eq, hs_star_def]
      rw [show -(Au - c * Av) * (-(Au - c * Av) / (1 - c ^ 2)) =
            ((-(Au - c * Av)) * (-(Au - c * Av))) / (1 - c ^ 2) from by ring]
      congr 1
      ring
    have hineq : (Au - c * Av) ^ 2 / (1 - c ^ 2) ≤ ‖A_perp‖ ^ 2 := by
      rw [div_le_iff₀ h_one_minus_c_sq_pos]
      linarith [h_CS]
    have h_expand : (1 - c ^ 2) * (s₂ - s_star) ^ 2 =
        s₂ ^ 2 * (1 - c ^ 2) - 2 * s₂ * ((1 - c ^ 2) * s_star) +
        (1 - c ^ 2) * s_star ^ 2 := by ring
    rw [h_expand, h_star_eq, h_star_sq]
    linarith [hineq]
  have h_final_sq : (1 - c ^ 2) * (s₂ - s_star) ^ 2 ≤ (2 * δ + r) ^ 2 := by
    calc (1 - c ^ 2) * (s₂ - s_star) ^ 2
        ≤ ‖A_perp + s₂ • u_perp‖ ^ 2 := h_completing_sq
      _ = ‖B - Bv • v‖ ^ 2 := by rw [← h_B_perp_eq]
      _ = ‖B‖ ^ 2 - Bv ^ 2 := h_perp_norm_sq
      _ ≤ ‖B‖ ^ 2 := by linarith [sq_nonneg Bv]
      _ ≤ (2 * δ + r) ^ 2 := hB_norm_sq
  have h_θ_sq_bound : (θ ^ 2 / 2) * (s₂ - s_star) ^ 2 ≤ (2 * δ + r) ^ 2 := by
    calc (θ ^ 2 / 2) * (s₂ - s_star) ^ 2
        ≤ (1 - c ^ 2) * (s₂ - s_star) ^ 2 := by
          apply mul_le_mul_of_nonneg_right h_one_minus_c_sq (sq_nonneg _)
      _ ≤ (2 * δ + r) ^ 2 := h_final_sq
  have h_s2_bound : |s₂ - s_star| ≤ Real.sqrt 2 * (2 * δ + r) / θ := by
    have hθ_sq_pos : 0 < θ ^ 2 := by positivity
    have h1 : (s₂ - s_star) ^ 2 ≤ 2 * (2 * δ + r) ^ 2 / θ ^ 2 := by
      rw [le_div_iff₀ hθ_sq_pos]
      linarith [h_θ_sq_bound]
    have h2 : (s₂ - s_star) ^ 2 ≤ (Real.sqrt 2 * (2 * δ + r) / θ) ^ 2 := by
      have h_rhs_sq : (Real.sqrt 2 * (2 * δ + r) / θ) ^ 2 =
          2 * (2 * δ + r) ^ 2 / θ ^ 2 := by
        rw [div_pow]
        congr 1
        rw [mul_pow]
        rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      rw [h_rhs_sq]
      exact h1
    have h_rhs_nn : 0 ≤ Real.sqrt 2 * (2 * δ + r) / θ := by
      have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      positivity
    exact abs_le_of_sq_le_sq h2 h_rhs_nn
  set s : ℝ := (inner ℝ (p - T_i.midpoint) u : ℝ) with hs_def
  have h_s_s2 : |s - s₂| ≤ δ := by
    have h_inner_eq : (inner ℝ (p - T_i.midpoint - s₂ • u) u : ℝ) = s - s₂ := by
      rw [inner_sub_left, inner_smul_left, h_inner_uu, RCLike.conj_to_real, mul_one]
    have h_abs_le : |(inner ℝ (p - T_i.midpoint - s₂ • u) u : ℝ)| ≤
        ‖p - T_i.midpoint - s₂ • u‖ * ‖u‖ :=
      abs_real_inner_le_norm _ _
    rw [hu_norm, mul_one, h_inner_eq] at h_abs_le
    exact h_abs_le.trans hp_T2_norm
  have h_final : |s - s_star| ≤ δ + Real.sqrt 2 * (2 * δ + r) / θ := by
    have h_tri : |s - s_star| ≤ |s - s₂| + |s₂ - s_star| := by
      have heq : s - s_star = (s - s₂) + (s₂ - s_star) := by ring
      rw [heq]; exact abs_add_le _ _
    linarith [h_tri, h_s_s2, h_s2_bound]
  exact h_final

/-- The dimensional constant in `vol_inter_carrier_cthickening_le`. -/
noncomputable def intersectionVolumeConstant
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ :=
  let n := Module.finrank ℝ E
  2 * (2 + 101 * Real.sqrt 2) *
    (Real.sqrt Real.pi ^ (n - 1) / Real.Gamma ((n - 1 : ℕ) / 2 + 1))

/-- The tube-intersection volume constant is positive. -/
lemma intersectionVolumeConstant_pos
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    0 < intersectionVolumeConstant E := by
  unfold intersectionVolumeConstant
  have h_sqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h_gamma_pos :
      0 < Real.Gamma ((Module.finrank ℝ E - 1 : ℕ) / 2 + 1) := by
    apply Real.Gamma_pos_of_pos
    positivity
  positivity

/-- **Helper 3 (intersection volume chord bound).** For tubes
`T_i, T₀' : Tube δ E` with `δ ∈ (0, 1]`, suppose
`‖T₀'.direction - T_i.direction‖ ≤ ‖T₀'.direction + T_i.direction‖`
(WLOG choice of the smaller representative) and
`θ := ‖T₀'.direction - T_i.direction‖ > 0`. Then there is a uniform
dimension-only constant `C(n) > 0` such that
`vol (T_i.carrier ∩ cthickening (99·δ) T₀'.carrier) ≤ C · δ^n / θ`. -/
lemma vol_inter_carrier_cthickening_le
    [Nontrivial E] {δ : NNReal} (hδ_pos : 0 < δ) (_hδ_le : δ ≤ 1)
    (T_i T₀' : Tube δ E)
    (h_dir_min :
      ‖T₀'.direction - T_i.direction‖ ≤ ‖T₀'.direction + T_i.direction‖)
    (h_θ_pos : 0 < ‖T₀'.direction - T_i.direction‖) :
    volume (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
      ENNReal.ofReal (intersectionVolumeConstant E * δ ^ (Module.finrank ℝ E) /
        ‖T₀'.direction - T_i.direction‖) := by
  set n : ℕ := Module.finrank ℝ E with hn_def
  set C_perp : ℝ :=
    Real.sqrt Real.pi ^ (n - 1) / Real.Gamma ((n - 1 : ℕ) / 2 + 1) with hCperp_def
  have hC_perp_pos : 0 < C_perp := by
    have h_sqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h_pow_pos : 0 < Real.sqrt Real.pi ^ (n - 1) := pow_pos h_sqrt_pi_pos _
    have h_gamma_pos : 0 < Real.Gamma ((n - 1 : ℕ) / 2 + 1) := by
      apply Real.Gamma_pos_of_pos
      positivity
    exact div_pos h_pow_pos h_gamma_pos
  have hn_pos : 0 < n := Module.finrank_pos
  have hδr_pos : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ_pos
  set θ : ℝ := ‖T₀'.direction - T_i.direction‖ with hθ_def
  have hθ_pos : 0 < θ := h_θ_pos
  have hu_norm : ‖T_i.direction‖ = 1 := by
    have := T_i.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have hv_norm : ‖T₀'.direction‖ = 1 := by
    have := T₀'.dist_eq_one
    rwa [dist_eq_norm, ← neg_sub, norm_neg] at this
  have hθ_le_two : θ ≤ 2 := by
    have := norm_sub_le T₀'.direction T_i.direction
    rw [hu_norm, hv_norm] at this
    linarith [this, hθ_def]
  have h_99δ_nn : (0 : ℝ) ≤ 99 * δ := by linarith [hδ_pos.le]
  obtain ⟨s_star, hs_star⟩ :=
    exists_axis_param_bound_thick (δ := δ) hδ_pos h_99δ_nn T₀' T_i h_dir_min h_θ_pos
  set L : ℝ := δ + Real.sqrt 2 * (2 * δ + 99 * δ) / θ with hL_def
  have hL_eq : L = δ + Real.sqrt 2 * (101 * δ) / θ := by
    rw [hL_def]; ring_nf
  set d : E := T_i.direction with hd_def
  set m : E := T_i.midpoint with hm_def
  have h_inter_sub :
      T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier ⊆
        cylinder m d (s_star - L) (s_star + L) δ := by
    intro p hp
    obtain ⟨hp_i, hp_thick⟩ := hp
    have h_axis : |(inner ℝ (p - T_i.midpoint) T_i.direction : ℝ) - s_star| ≤ L :=
      hs_star p ⟨hp_thick, hp_i⟩
    have h_axis_le := abs_le.mp h_axis
    have h_self : p ∈ cylinder T_i.midpoint T_i.direction (-(1/2) - δ) (1/2 + δ) δ :=
      _root_.Tube.carrier_subset_cylinder_self T_i hδ_pos.le hp_i
    rw [mem_cylinder] at h_self
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · linarith [h_axis_le.1]
    · linarith [h_axis_le.2]
    · exact h_self.2
  have h_cyl_meas : MeasurableSet (cylinder m d (s_star - L) (s_star + L) δ) :=
    (isClosed_cylinder m d (s_star - L) (s_star + L) δ).measurableSet
  have h_vol_le : volume (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
      volume (cylinder m d (s_star - L) (s_star + L) δ) :=
    measure_mono h_inter_sub
  have hd_norm : ‖d‖ = 1 := hu_norm
  have h_cyl_vol :
      volume (cylinder m d (s_star - L) (s_star + L) δ) =
        ENNReal.ofReal ((s_star + L) - (s_star - L)) *
          volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) δ) :=
    volume_cylinder hd_norm m (s_star - L) (s_star + L) δ
  have hd_ne : d ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd_norm
    norm_num at hd_norm
  have h_finrank_perp :
      Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E) = n - 1 := by
    have h1 : Module.finrank ℝ (ℝ ∙ d) = 1 := finrank_span_singleton hd_ne
    have h2 : Module.finrank ℝ (ℝ ∙ d) + Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E) =
        Module.finrank ℝ E :=
      Submodule.finrank_add_finrank_orthogonal _
    rw [h1] at h2
    omega
  have h_perp_ball_vol :
      volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) δ) ≤
        (ENNReal.ofReal δ) ^ (n - 1) *
          ENNReal.ofReal
            (Real.sqrt Real.pi ^ (n - 1) /
              Real.Gamma ((n - 1 : ℕ) / 2 + 1)) := by
    by_cases h_perp_trivial : Nontrivial ((ℝ ∙ d)ᗮ : Submodule ℝ E)
    · have h_perp_eq :
          volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) δ) =
            (ENNReal.ofReal δ) ^
              (Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E)) *
              ENNReal.ofReal
                (Real.sqrt Real.pi ^
                  (Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E)) /
                  Real.Gamma
                    ((Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E) : ℕ) / 2 + 1)) :=
        InnerProductSpace.volume_closedBall _ _
      rw [h_perp_eq, h_finrank_perp]
    · have h_subsing : Subsingleton ((ℝ ∙ d)ᗮ : Submodule ℝ E) := by
        rw [not_nontrivial_iff_subsingleton] at h_perp_trivial
        exact h_perp_trivial
      have h_perp_zero :
          Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E) = 0 := by
        rw [Module.finrank_zero_iff]
        exact h_subsing
      have hn_eq_one : n = 1 := by omega
      have h_ball_eq_univ :
          Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) δ = Set.univ := by
        ext x
        refine ⟨fun _ => trivial, fun _ => ?_⟩
        rw [Metric.mem_closedBall]
        have hx : x = 0 := Subsingleton.elim x 0
        rw [hx, dist_self]
        exact hδ_pos.le
      have h_vol_univ : volume (Set.univ : Set ((ℝ ∙ d)ᗮ : Submodule ℝ E)) = 1 := by
        rw [show (volume : Measure ((ℝ ∙ d)ᗮ : Submodule ℝ E))
              = (stdOrthonormalBasis ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E)).toBasis.addHaar from rfl]
        have h_para_univ :
            _root_.parallelepiped
              (stdOrthonormalBasis ℝ
                ((ℝ ∙ d)ᗮ : Submodule ℝ E)).toBasis = (Set.univ : Set _) := by
          ext x
          have hx : x = 0 := Subsingleton.elim x 0
          refine ⟨fun _ => trivial, fun _ => ?_⟩
          rw [hx]
          refine ⟨fun _ => 0, ?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · intro i; rfl
            · intro i; exact zero_le_one
          · simp
        rw [← h_para_univ]
        exact (stdOrthonormalBasis ℝ
          ((ℝ ∙ d)ᗮ : Submodule ℝ E)).toBasis.addHaar_self
      rw [h_ball_eq_univ, h_vol_univ, hn_eq_one]
      simp
  have h_2L : (s_star + L) - (s_star - L) = 2 * L := by ring
  rw [h_2L] at h_cyl_vol
  have hsqrt2_nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hL_nn : 0 ≤ L := by
    rw [hL_def]
    have : 0 ≤ Real.sqrt 2 * (2 * δ + 99 * δ) / θ := by
      apply div_nonneg
      · apply mul_nonneg hsqrt2_nn
        linarith
      · exact hθ_pos.le
    linarith [hδ_pos.le, this]
  have h_2L_nn : 0 ≤ 2 * L := by linarith
  have hδ_pow_nn : (0 : ℝ) ≤ δ ^ (n - 1) := pow_nonneg hδ_pos.le _
  have h_perp_const_nn :
      (0 : ℝ) ≤ Real.sqrt Real.pi ^ (n - 1) / Real.Gamma ((n - 1 : ℕ) / 2 + 1) :=
    hC_perp_pos.le
  have h_2LdC_nn : 0 ≤ 2 * L * δ ^ (n - 1) * C_perp := by
    apply mul_nonneg
    · exact mul_nonneg h_2L_nn hδ_pow_nn
    · exact hC_perp_pos.le
  have h_cyl_vol_le :
      volume (cylinder m d (s_star - L) (s_star + L) δ) ≤
        ENNReal.ofReal (2 * L * δ ^ (n - 1) * C_perp) := by
    rw [h_cyl_vol]
    have h_RHS_eq :
        ENNReal.ofReal (2 * L * δ ^ (n - 1) * C_perp) =
          ENNReal.ofReal (2 * L) *
            ((ENNReal.ofReal δ) ^ (n - 1) * ENNReal.ofReal C_perp) := by
      rw [← ENNReal.ofReal_pow hδr_pos.le]
      rw [← ENNReal.ofReal_mul hδ_pow_nn]
      rw [← ENNReal.ofReal_mul h_2L_nn]
      ring_nf
    rw [h_RHS_eq]
    apply mul_le_mul_of_nonneg_left
    · exact h_perp_ball_vol
    · exact bot_le
  have h_vol_le' :
      volume (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
        ENNReal.ofReal (2 * L * δ ^ (n - 1) * C_perp) :=
    h_vol_le.trans h_cyl_vol_le
  have h_vol_real_le :
      volume.real (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
        2 * L * δ ^ (n - 1) * C_perp := by
    have h_ne_top :
        volume (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≠ ⊤ := by
      have h_le_top : volume (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
          ENNReal.ofReal (2 * L * δ ^ (n - 1) * C_perp) := h_vol_le'
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_le_top
    unfold Measure.real
    rw [show (2 * L * δ ^ (n - 1) * C_perp : ℝ) =
          ENNReal.toReal (ENNReal.ofReal (2 * L * δ ^ (n - 1) * C_perp)) from
      (ENNReal.toReal_ofReal h_2LdC_nn).symm]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h_vol_le'
  have h_2δ_le : 2 * δ ≤ 4 * δ / θ := by
    have h2_θ_ge_1 : 1 ≤ 2 / θ := by
      rw [le_div_iff₀ hθ_pos]
      linarith [hθ_le_two]
    have : 2 * δ * 1 ≤ 2 * δ * (2 / θ) := by
      apply mul_le_mul_of_nonneg_left h2_θ_ge_1
      linarith [hδ_pos.le]
    have heq : 2 * δ * (2 / θ) = 4 * δ / θ := by
      field_simp
      ring
    linarith [this, heq]
  have h_2L_bound : 2 * L ≤ (4 + 202 * Real.sqrt 2) * δ / θ := by
    rw [hL_def]
    have h_2δ_part : 2 * δ ≤ 4 * δ / θ := h_2δ_le
    have h_sqrt_part : 2 * (Real.sqrt 2 * (2 * (δ : ℝ) + 99 * δ) / θ) =
        202 * Real.sqrt 2 * δ / θ := by
      have : (2 * (δ : ℝ) + 99 * δ) = 101 * δ := by ring
      rw [this]
      field_simp
      ring
    have h_2L_eq :
        2 * (δ + Real.sqrt 2 * (2 * δ + 99 * δ) / θ) =
          2 * δ + 2 * (Real.sqrt 2 * (2 * δ + 99 * δ) / θ) := by ring
    rw [h_2L_eq, h_sqrt_part]
    have h_add :
        (4 + 202 * Real.sqrt 2) * δ / θ = 4 * δ / θ + 202 * Real.sqrt 2 * δ / θ := by
      field_simp
    rw [h_add]
    linarith [h_2δ_part]
  have hδ_pow_pos : 0 < δ ^ (n - 1) := pow_pos hδ_pos _
  have h_mul_bound :
      2 * L * δ ^ (n - 1) * C_perp ≤
        ((4 + 202 * Real.sqrt 2) * δ / θ) * δ ^ (n - 1) * C_perp := by
    have h1 : 2 * L * δ ^ (n - 1) ≤ ((4 + 202 * Real.sqrt 2) * δ / θ) * δ ^ (n - 1) :=
      mul_le_mul_of_nonneg_right h_2L_bound hδ_pow_nn
    exact mul_le_mul_of_nonneg_right h1 hC_perp_pos.le
  have hn_pos' : 0 < n := Module.finrank_pos
  have hn_succ : n = (n - 1) + 1 := by omega
  have hδ_pow : ((δ : ℝ) ^ n : ℝ) = (δ : ℝ) ^ (n - 1) * (δ : ℝ) := by
    conv_lhs => rw [hn_succ]
    rw [pow_succ]
  have h_calc :
      ((4 + 202 * Real.sqrt 2) * (δ : ℝ) / θ) * (δ : ℝ) ^ (n - 1) * C_perp =
        (2 * (2 + 101 * Real.sqrt 2)) * C_perp * (δ : ℝ) ^ n / θ := by
    rw [hδ_pow]
    field_simp
    ring
  have hfinal_real :
      volume.real (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≤
        intersectionVolumeConstant E * δ ^ Module.finrank ℝ E / θ := by
    calc volume.real (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier)
        ≤ 2 * L * δ ^ (n - 1) * C_perp := h_vol_real_le
      _ ≤ ((4 + 202 * Real.sqrt 2) * δ / θ) * δ ^ (n - 1) * C_perp := h_mul_bound
      _ = (2 * (2 + 101 * Real.sqrt 2)) * C_perp * δ ^ n / θ := h_calc
      _ = intersectionVolumeConstant E * δ ^ Module.finrank ℝ E / θ := by
          rw [intersectionVolumeConstant, ← hn_def, ← hCperp_def]
  have hRHS_nn :
      0 ≤ intersectionVolumeConstant E * (δ : ℝ) ^ Module.finrank ℝ E / θ := by
    exact div_nonneg
      (mul_nonneg (intersectionVolumeConstant_pos E).le (pow_nonneg hδr_pos.le _))
      hθ_pos.le
  have hLHS_fin :
      volume (T_i.carrier ∩ Metric.cthickening (99 * δ) T₀'.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top T_i.isCompact.measure_lt_top.ne
      (measure_mono Set.inter_subset_left)
  refine (ENNReal.toReal_le_toReal hLHS_fin ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal]
  · simpa [Measure.real, hθ_def, hn_def, hd_def] using hfinal_real
  · simpa [hθ_def, hn_def, hd_def] using hRHS_nn

/-- The dimensional constant used for ball-slice intersection volume bounds. -/
noncomputable def sliceIntersectionVolumeConstant
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : ℝ :=
  let n := Module.finrank ℝ E
  2 * (100 : ℝ) ^ (n - 1) *
    (Real.sqrt Real.pi ^ (n - 1) / Real.Gamma ((n - 1 : ℕ) / 2 + 1))

/-- The ball-slice intersection volume constant is positive. -/
lemma sliceIntersectionVolumeConstant_pos
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    0 < sliceIntersectionVolumeConstant E := by
  unfold sliceIntersectionVolumeConstant
  have h_sqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h_gamma_pos :
      0 < Real.Gamma ((Module.finrank ℝ E - 1 : ℕ) / 2 + 1) := by
    apply Real.Gamma_pos_of_pos
    positivity
  positivity

end
end Kakeya.Tube
