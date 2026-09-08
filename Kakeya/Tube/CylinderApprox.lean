/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Geometry.Cylinder
public import Kakeya.Tube.Basic

/-!
# Cylinder approximation of tube carriers

Pure geometric API relating a `Tube`'s carrier to axis-aligned cylinders
(`cylinder`) and `cthickening`s: a tube carrier sits inside the cylinder around
its own axis, slab cylinders sit inside the carrier, and the intersection of two
tubes is confined to a thin slab whose axial extent is controlled by the angle
between the directions. These facts contain no essential-distinctness content;
they are the reusable geometry feeding the tube-intersection volume bounds.
-/

open MeasureTheory ENNReal

namespace Tube

variable
  {δ : NNReal}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

@[expose] public section

/-- Rewriting of a convex combination `α • x + β • y` (with `α + β = 1`) as the
midpoint of `x, y` shifted by `β - 1/2` times the direction `y - x`.
Stated over a bare `Module ℝ M` so that `module` never has to traverse the
`InnerProductSpace` instance chain. -- (extracted by Fuse golfer) -/
private lemma smul_add_smul_eq_midpoint_add_smul_sub
    {M : Type*} [AddCommGroup M] [Module ℝ M] {α β : ℝ} (hαβ : α + β = 1) (x y : M) :
    α • x + β • y = (1 / 2 : ℝ) • (x + y) + (β - 1 / 2) • (y - x) := by
  rw [show α = 1 - β from by linarith only [hαβ]]
  module

/-- Decomposition of `p - (m₁ + (s - t) • v)` into a perpendicular offset, a
radial offset and a direction-error term.  Stated over a bare `Module ℝ M` for
the same elaboration-cost reason. -- (extracted by Fuse golfer) -/
private lemma sub_axis_point_eq {M : Type*} [AddCommGroup M] [Module ℝ M]
    (p m₁ m₂ u v : M) (s t : ℝ) :
    p - (m₁ + (s - t) • v) =
      -((m₁ - m₂) - t • u) + ((p - m₂) - s • u) - (s - t) • (v - u) := by
  module

/-- Every tube carrier is contained in the cylinder around its own axis of
half-length `1/2 + δ` and radius `δ`. -/
lemma carrier_subset_cylinder_self (T : Tube δ E) (hδ : 0 ≤ δ) :
    T.carrier ⊆ cylinder T.midpoint T.direction (-(1 / 2) - δ) (1 / 2 + δ) δ := by
  intro p hp
  rw [T.carrier_eq] at hp
  obtain ⟨z, ⟨α, β, hα, hβ, hαβ, hz_eq⟩, hpz⟩ := Set.mem_iUnion₂.mp hp
  have hs_lb : -(1 / 2 : ℝ) ≤ β - 1 / 2 := by linarith only [hβ]
  have hs_ub : β - 1 / 2 ≤ 1 / 2 := by linarith only [hα, hαβ]
  have hz_alt : z = T.midpoint + (β - 1 / 2) • T.direction := by
    rw [← hz_eq]; exact smul_add_smul_eq_midpoint_add_smul_sub hαβ T.x T.y
  have hu_norm : ‖T.direction‖ = 1 := T.norm_direction
  -- Make the axis data opaque: `Tube.midpoint`/`Tube.direction` are reducible
  -- abbreviations, so leaving them exposed makes every later `module`/`linarith`
  -- atom comparison unfold them.
  set u : E := T.direction with hu_def
  set m : E := T.midpoint with hm_def
  set s : ℝ := β - 1 / 2 with hs_def
  obtain ⟨d, hd_norm, hd_eq⟩ : ∃ d : E, ‖d‖ ≤ δ ∧ p - m - s • u = d :=
    ⟨p - z, by rw [← dist_eq_norm]; exact hpz, by rw [sub_sub, hz_alt]⟩
  clear_value u m s
  have hpm : p - m = d + s • u := sub_eq_iff_eq_add.mp hd_eq
  obtain ⟨e, he_def⟩ : ∃ r : ℝ, r = (inner ℝ d u : ℝ) := ⟨_, rfl⟩
  have huu : (inner ℝ u u : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hu_norm, one_pow]
  have h_inner : (inner ℝ (p - m) u : ℝ) = e + s := by
    rw [hpm, inner_add_left, inner_smul_left, huu, RCLike.conj_to_real, mul_one, he_def]
  obtain ⟨he₁, he₂⟩ : -(δ : ℝ) ≤ e ∧ e ≤ (δ : ℝ) := by
    refine abs_le.mp ?_
    have h := abs_real_inner_le_norm d u
    rw [hu_norm, mul_one, ← he_def] at h
    exact h.trans hd_norm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h_inner]; linarith only [he₁, hs_lb]
  · rw [h_inner]; linarith only [he₂, hs_ub]
  · rw [h_inner, hpm, add_smul, add_sub_add_right_eq_sub]
    have hsq : ‖d - e • u‖ ^ 2 ≤ (δ : ℝ) ^ 2 := by
      rw [@norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        hu_norm, ← he_def]
      linarith only [pow_le_pow_left₀ (norm_nonneg d) hd_norm 2, sq_nonneg e]
    have h2 := abs_le_of_sq_le_sq hsq hδ
    rwa [abs_of_nonneg (norm_nonneg _)] at h2

/-- If `[a, b] ⊆ [-1/2, 1/2]` and `r ≤ δ`, the cylinder
`cylinder T.midpoint T.direction a b r` is contained in `T.carrier`. -/
lemma cylinder_subset_carrier_self
    (T : Tube δ E)
    {a b r : ℝ} (ha : -(1 / 2 : ℝ) ≤ a) (hb : b ≤ 1 / 2) (hr : r ≤ δ) :
    cylinder T.midpoint T.direction a b r ⊆ T.carrier := by
  intro p hp
  rw [mem_cylinder] at hp
  obtain ⟨hs_mem, hperp⟩ := hp
  set s : ℝ := inner ℝ (p - T.midpoint) T.direction with hs_def
  set z : E := T.midpoint + s • T.direction with hz_def
  have hs_l : -(1 / 2 : ℝ) ≤ s := ha.trans hs_mem.1
  have hs_r : s ≤ 1 / 2 := hs_mem.2.trans hb
  have hz_seg : z ∈ segment ℝ T.x T.y :=
    T.midpoint_add_smul_direction_mem_segment hs_l hs_r
  have hball : Metric.closedBall z δ ⊆ T.carrier :=
    T.closedBall_subset_carrier_of_mem_segment hz_seg
  apply hball
  rw [Metric.mem_closedBall, dist_eq_norm]
  have heq : p - z = (p - T.midpoint) - s • T.direction := by
    change p - (T.midpoint + s • T.direction) = (p - T.midpoint) - s • T.direction
    abel
  rw [heq]
  exact hperp.trans hr

/-- Two tubes T₁, T₂ with direction-closeness and perp-midpoint bounds. A
cylinder centred at `T₂.midpoint`, along `T₂.direction`, whose parameter range
`[a, b]` is translated to align with T₁'s segment and whose radius is at most
`(1 - 2c)·δ`, is contained in `T₁.carrier`. -/
lemma cylinder_T2_subset_T1_carrier
    {T₁ T₂ : Tube δ E} (_hδ_pos : 0 < δ)
    {c : ℝ} (hc_nn : 0 ≤ c)
    (h_dir : ‖T₁.direction - T₂.direction‖ ≤ c * δ)
    (h_perp : ‖(T₁.midpoint - T₂.midpoint) -
              (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction : ℝ) • T₂.direction‖
              ≤ c * δ)
    {a b r : ℝ}
    (h_a : inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction - (1 / 2 : ℝ) ≤ a)
    (h_b : b ≤ inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction + (1 / 2 : ℝ))
    (h_r_le : r ≤ (1 - 2 * c) * δ) :
    cylinder T₂.midpoint T₂.direction a b r ⊆ T₁.carrier := by
  intro p hp
  obtain ⟨hs_mem, hq_norm⟩ := hp
  -- Make the axis data opaque: `Tube.midpoint`/`Tube.direction` are reducible
  -- abbreviations, so leaving them exposed makes every later `module`/`linarith`
  -- atom comparison unfold them.
  set u : E := T₂.direction with hu_def
  set v : E := T₁.direction with hv_def
  set m₁ : E := T₁.midpoint with hm₁_def
  set m₂ : E := T₂.midpoint with hm₂_def
  set t : ℝ := (inner ℝ (m₁ - m₂) u : ℝ) with ht_def
  set s : ℝ := (inner ℝ (p - m₂) u : ℝ) with hs_def
  have hlb : -(1 / 2 : ℝ) ≤ s - t := by linarith only [h_a.trans hs_mem.1]
  have hub : s - t ≤ 1 / 2 := by linarith only [hs_mem.2.trans h_b]
  have hz_seg := T₁.midpoint_add_smul_direction_mem_segment (s := s - t) hlb hub
  rw [← hv_def, ← hm₁_def] at hz_seg
  refine T₁.closedBall_subset_carrier_of_mem_segment hz_seg ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  clear_value s t
  clear_value u v m₁ m₂
  have hb1 : ‖-((m₁ - m₂) - t • u) + ((p - m₂) - s • u)‖ ≤ c * δ + (1 - 2 * c) * δ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    exact add_le_add h_perp (hq_norm.trans h_r_le)
  have hb2 : ‖(s - t) • (v - u)‖ ≤ 1 / 2 * (c * δ) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_le.mpr ⟨hlb, hub⟩) h_dir (norm_nonneg _) (by norm_num)
  rw [sub_axis_point_eq p m₁ m₂ u v s t]
  refine (norm_sub_le _ _).trans ((add_le_add hb1 hb2).trans ?_)
  linarith only [mul_nonneg hc_nn δ.coe_nonneg]

/-- Every point of a tube carrier lies within `δ` of some point of the axis line
`T.midpoint + s • T.direction`. -- (extracted by Fuse golfer) -/
private lemma exists_axis_param_of_mem_carrier
    {T : Tube δ E} {p : E} (hp : p ∈ T.carrier) :
    ∃ s : ℝ, ‖p - T.midpoint - s • T.direction‖ ≤ δ := by
  rw [T.carrier_eq] at hp
  obtain ⟨z, hz_seg, hpz⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨α, β, _, _, hαβ, hz_eq⟩ := hz_seg
  refine ⟨β - 1 / 2, ?_⟩
  have hz_alt : z = T.midpoint + (β - 1 / 2) • T.direction := by
    rw [← hz_eq]
    change α • T.x + β • T.y = (1/2 : ℝ) • (T.x + T.y) + (β - 1/2) • (T.y - T.x)
    rw [show α = 1 - β from by linarith only [hαβ]]
    module
  rw [show p - T.midpoint - (β - 1 / 2) • T.direction = p - z from by rw [hz_alt]; abel,
    ← dist_eq_norm]
  exact hpz

/-- Closest-approach bound. For two tubes T₁, T₂ with directions making angle
parameter `θ := ‖T₁.direction - T₂.direction‖ > 0` (after WLOG sign-flip,
`θ ≤ ‖T₁.direction + T₂.direction‖`), every point `p` in `T₁ ∩ T₂` has its
`T₂`-axis parameter `inner (p - T₂.midpoint) T₂.direction` within
`δ + 2√2·δ/θ` of a single real number `s*` (depending only on T₁, T₂, δ). -/
lemma exists_axis_param_bound
    (hδ_pos : 0 < δ) (T₁ T₂ : Tube δ E)
    (h_dir_min :
      ‖T₁.direction - T₂.direction‖ ≤ ‖T₁.direction + T₂.direction‖)
    (h_θ_pos : 0 < ‖T₁.direction - T₂.direction‖) :
    ∃ s_star : ℝ, ∀ p ∈ T₁.carrier ∩ T₂.carrier,
      |inner ℝ (p - T₂.midpoint) T₂.direction - s_star| ≤
        (δ : ℝ) + 2 * Real.sqrt 2 * (δ : ℝ) / ‖T₁.direction - T₂.direction‖ := by
  -- Unit vectors u (= T₂.direction), v (= T₁.direction).
  set u : E := T₂.direction with hu_def
  set v : E := T₁.direction with hv_def
  have hu_norm : ‖u‖ = 1 := T₂.norm_direction
  have hv_norm : ‖v‖ = 1 := T₁.norm_direction
  have h_inner_uu : (inner ℝ u u : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hu_norm, one_pow]
  have h_inner_vv : (inner ℝ v v : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, hv_norm, one_pow]
  -- θ := ‖v - u‖.
  set θ : ℝ := ‖v - u‖ with hθ_def
  have hθ_pos : 0 < θ := h_θ_pos
  -- c := ⟨u, v⟩.
  set c : ℝ := (inner ℝ u v : ℝ) with hc_def
  -- Make `u, v, θ, c` opaque: `Tube.direction`/`Tube.midpoint` are reducible
  -- abbreviations, so leaving them as local definitions makes every later
  -- `ring`/`linarith`/`module` atom comparison unfold them.
  clear_value u v θ c
  -- c = ⟨v, u⟩ by symmetry.
  have h_inner_vu : (inner ℝ v u : ℝ) = c := by
    rw [hc_def, real_inner_comm]
  -- θ² = 2 - 2c.
  have hθ_sq : θ ^ 2 = 2 - 2 * c := by
    have := @norm_sub_sq_real _ _ _ v u
    rw [hv_norm, hu_norm, h_inner_vu, ← hθ_def] at this
    linarith only [this]
  -- ‖v + u‖² = 2 + 2c.
  have h_add_sq : ‖v + u‖ ^ 2 = 2 + 2 * c := by
    have := @norm_add_sq_real _ _ _ v u
    rw [hv_norm, hu_norm, h_inner_vu] at this
    linarith only [this]
  -- From h_dir_min: θ² ≤ ‖v+u‖² = 2 + 2c, so c ≥ θ²/2 - 1.
  -- Also from θ² = 2 - 2c: c = 1 - θ²/2.
  have hc_eq : c = 1 - θ ^ 2 / 2 := by linarith only [hθ_sq]
  -- From θ ≤ ‖v + u‖: θ² ≤ ‖v+u‖² so 2 - 2c ≤ 2 + 2c, i.e., c ≥ 0.
  have hc_nn : 0 ≤ c := by
    have h_sq : θ ^ 2 ≤ ‖v + u‖ ^ 2 :=
      pow_le_pow_left₀ hθ_pos.le h_dir_min 2
    rw [h_add_sq] at h_sq
    linarith only [h_sq, hθ_sq]
  -- θ² ≤ 2 (since c ≥ 0 and c = 1 - θ²/2 means θ²/2 ≤ 1)
  have hθ_sq_le_two : θ ^ 2 ≤ 2 := by linarith only [hc_eq, hc_nn]
  -- 1 - c² ≥ θ²/2.
  have h_one_minus_c_sq : θ ^ 2 / 2 ≤ 1 - c ^ 2 := by
    -- c = 1 - θ²/2, so c² = 1 - θ² + θ⁴/4, so 1 - c² = θ² - θ⁴/4.
    -- θ² - θ⁴/4 ≥ θ²/2 iff θ²/2 ≥ θ⁴/4 iff 2θ² ≥ θ⁴ iff θ² ≤ 2 (when θ² > 0).
    have h := mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hθ_sq_le_two)
    rw [hc_eq]
    linarith only [h]
  -- 1 - c² > 0.
  have h_one_minus_c_sq_pos : 0 < 1 - c ^ 2 :=
    lt_of_lt_of_le (by positivity) h_one_minus_c_sq
  -- A := T₂.midpoint - T₁.midpoint.
  obtain ⟨A, hA_def⟩ : ∃ A : E, A = T₂.midpoint - T₁.midpoint := ⟨_, rfl⟩
  obtain ⟨Au, hAu_def⟩ : ∃ r : ℝ, r = (inner ℝ A u : ℝ) := ⟨_, rfl⟩
  obtain ⟨Av, hAv_def⟩ : ∃ r : ℝ, r = (inner ℝ A v : ℝ) := ⟨_, rfl⟩
  -- s_star := -(Au - c * Av) / (1 - c²).
  obtain ⟨s_star, hs_star_def⟩ :
      ∃ r : ℝ, r = -(Au - c * Av) / (1 - c ^ 2) := ⟨_, rfl⟩
  refine ⟨s_star, ?_⟩
  rintro p ⟨hp1, hp2⟩
  -- Axis parameters s₁, s₂ realising the distance to each tube's axis.
  obtain ⟨s₁, hp_T1_norm⟩ := exists_axis_param_of_mem_carrier hp1
  obtain ⟨s₂, hp_T2_norm⟩ := exists_axis_param_of_mem_carrier hp2
  rw [← hv_def] at hp_T1_norm
  rw [← hu_def] at hp_T2_norm
  -- B := A + s₂ • u - s₁ • v. Then ‖B‖ ≤ 2δ.
  obtain ⟨B, hB_def⟩ : ∃ B : E, B = A + s₂ • u - s₁ • v := ⟨_, rfl⟩
  have hB_id : B = -(p - T₂.midpoint - s₂ • u) + (p - T₁.midpoint - s₁ • v) := by
    simp only [hB_def, hA_def]; abel
  have hB_norm : ‖B‖ ≤ 2 * δ := by
    rw [hB_id]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg]
    linarith only [hp_T1_norm, hp_T2_norm]
  -- Now ‖B‖² ≤ 4δ².
  have hB_norm_sq : ‖B‖ ^ 2 ≤ 4 * δ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg B) hB_norm 2
    linarith only [this]
  -- Compute inner ℝ B v.
  have h_inner_Bv : (inner ℝ B v : ℝ) = Av + s₂ * c - s₁ := by
    simp only [hB_def]
    -- inner A v = Av, inner u v = c (note c = inner ℝ u v).
    rw [inner_sub_left, inner_add_left, inner_smul_left, inner_smul_left,
        h_inner_vv, RCLike.conj_to_real, RCLike.conj_to_real, ← hc_def, ← hAv_def, mul_one]
  -- Pythagoras: ‖B‖² = ⟨B,v⟩² + ‖B - ⟨B,v⟩ • v‖² since ‖v‖ = 1.
  -- Equivalently: ‖B - ⟨B,v⟩ • v‖² ≤ ‖B‖².
  set Bv : ℝ := (inner ℝ B v : ℝ) with hBv_def
  have h_perp_norm_sq : ‖B - Bv • v‖ ^ 2 = ‖B‖ ^ 2 - Bv ^ 2 := by
    -- Expand ‖B - Bv • v‖² using norm_sub_sq_real.
    have h1 : ‖B - Bv • v‖ ^ 2 =
        ‖B‖ ^ 2 - 2 * (inner ℝ B (Bv • v) : ℝ) + ‖Bv • v‖ ^ 2 := by
      rw [@norm_sub_sq_real]
    rw [h1]
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hv_norm]
    change ‖B‖ ^ 2 - 2 * (Bv * Bv) + (Bv ^ 2 * 1 ^ 2) = ‖B‖ ^ 2 - Bv ^ 2
    ring
  -- Now compute B - Bv • v in terms of A_perp and u_perp.
  -- A_perp := A - Av • v (perp part of A w.r.t. v).
  -- u_perp := u - c • v (perp part of u w.r.t. v).
  obtain ⟨A_perp, hAperp_def⟩ : ∃ w : E, w = A - Av • v := ⟨_, rfl⟩
  obtain ⟨u_perp, huperp_def⟩ : ∃ w : E, w = u - c • v := ⟨_, rfl⟩
  -- B - Bv • v = A_perp + s₂ • u_perp.
  have h_B_perp_eq : B - Bv • v = A_perp + s₂ • u_perp := by
    rw [hAperp_def, huperp_def, hB_def, show Bv = Av + s₂ * c - s₁ from h_inner_Bv]
    module
  -- Now ‖A_perp + s₂ • u_perp‖² = ‖A_perp‖² + 2 s₂ ⟨A_perp, u_perp⟩ + s₂² ‖u_perp‖².
  -- We need ‖u_perp‖² = 1 - c², ⟨A_perp, u_perp⟩ = Au - c Av.
  have h_inner_Aperp_v : (inner ℝ A_perp v : ℝ) = 0 := by
    rw [hAperp_def, inner_sub_left, inner_smul_left, h_inner_vv,
        RCLike.conj_to_real, mul_one, ← hAv_def, sub_self]
  have h_uperp_norm_sq : ‖u_perp‖ ^ 2 = 1 - c ^ 2 := by
    have : ‖u_perp‖ ^ 2 = ‖u‖ ^ 2 - 2 * (inner ℝ u (c • v) : ℝ) + ‖c • v‖ ^ 2 := by
      rw [huperp_def, @norm_sub_sq_real]
    rw [this, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hu_norm,
      hv_norm, ← hc_def]
    ring
  have h_inner_Aperp_uperp : (inner ℝ A_perp u_perp : ℝ) = Au - c * Av := by
    -- A_perp ⊥ v, so inner(A_perp, u_perp) = inner(A_perp, u) - c * inner(A_perp, v)
    -- = inner(A_perp, u) = inner(A, u) - Av * inner(v, u) = Au - Av * c.
    have h_step1 : (inner ℝ A_perp u_perp : ℝ) =
        (inner ℝ A_perp u : ℝ) - c * (inner ℝ A_perp v : ℝ) := by
      rw [huperp_def, inner_sub_right, inner_smul_right]
    have h_step2 : (inner ℝ A_perp u : ℝ) = Au - Av * c := by
      have hsub : (inner ℝ A_perp u : ℝ) =
          (inner ℝ A u : ℝ) - Av * (inner ℝ v u : ℝ) := by
        rw [hAperp_def, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
      rw [hsub, h_inner_vu, ← hAu_def]
    rw [h_step1, h_step2, h_inner_Aperp_v]
    ring
  -- ‖A_perp + s₂ • u_perp‖² = ‖A_perp‖² + 2 s₂ (Au - c Av) + s₂² (1 - c²).
  have h_norm_perp_eq : ‖A_perp + s₂ • u_perp‖ ^ 2 =
      ‖A_perp‖ ^ 2 + 2 * s₂ * (Au - c * Av) + s₂ ^ 2 * (1 - c ^ 2) := by
    have h1 : ‖A_perp + s₂ • u_perp‖ ^ 2 =
        ‖A_perp‖ ^ 2 + 2 * (inner ℝ A_perp (s₂ • u_perp) : ℝ) + ‖s₂ • u_perp‖ ^ 2 := by
      rw [@norm_add_sq_real]
    rw [h1, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        h_inner_Aperp_uperp, h_uperp_norm_sq]
    ring
  -- Completing the square, we need (1 - c²)(s₂ - s_star)² ≤ ‖A_perp + s₂ • u_perp‖²
  -- ≤ ‖B‖² ≤ 4δ²; the first inequality comes from Cauchy-Schwarz on A_perp, u_perp.
  have h_CS : (Au - c * Av) ^ 2 ≤ ‖A_perp‖ ^ 2 * (1 - c ^ 2) := by
    rw [← h_uperp_norm_sq, ← h_inner_Aperp_uperp, ← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
  -- (1 - c²)(s₂ - s_star)² ≤ ‖A_perp + s₂ • u_perp‖².
  have h_completing_sq : (1 - c ^ 2) * (s₂ - s_star) ^ 2 ≤ ‖A_perp + s₂ • u_perp‖ ^ 2 := by
    rw [h_norm_perp_eq]
    -- Since s_star = -(Au - c Av)/(1 - c²), we have (1 - c²) s_star = -(Au - c Av),
    -- and Cauchy-Schwarz gives (1 - c²) s_star² ≤ ‖A_perp‖².
    have h_star_eq : (1 - c ^ 2) * s_star = -(Au - c * Av) := by
      rw [hs_star_def, mul_comm, div_mul_cancel₀ _ (ne_of_gt h_one_minus_c_sq_pos)]
    have h_star_sq : (1 - c ^ 2) * s_star ^ 2 ≤ ‖A_perp‖ ^ 2 := by
      refine le_of_mul_le_mul_right ?_ h_one_minus_c_sq_pos
      calc (1 - c ^ 2) * s_star ^ 2 * (1 - c ^ 2)
          = ((1 - c ^ 2) * s_star) ^ 2 := by ring
        _ = (Au - c * Av) ^ 2 := by rw [h_star_eq, neg_sq]
        _ ≤ ‖A_perp‖ ^ 2 * (1 - c ^ 2) := h_CS
    have h_expand : (1 - c ^ 2) * (s₂ - s_star) ^ 2 =
        s₂ ^ 2 * (1 - c ^ 2) - 2 * s₂ * ((1 - c ^ 2) * s_star) +
        (1 - c ^ 2) * s_star ^ 2 := by ring
    rw [h_expand, h_star_eq]
    linarith only [h_star_sq]
  -- (1 - c²)(s₂ - s_star)² ≤ 4δ².
  have h_final_sq : (1 - c ^ 2) * (s₂ - s_star) ^ 2 ≤ 4 * δ ^ 2 := by
    calc (1 - c ^ 2) * (s₂ - s_star) ^ 2
        ≤ ‖A_perp + s₂ • u_perp‖ ^ 2 := h_completing_sq
      _ = ‖B - Bv • v‖ ^ 2 := by rw [← h_B_perp_eq]
      _ = ‖B‖ ^ 2 - Bv ^ 2 := h_perp_norm_sq
      _ ≤ ‖B‖ ^ 2 := by linarith only [sq_nonneg Bv]
      _ ≤ 4 * δ ^ 2 := hB_norm_sq
  -- (θ²/2)(s₂ - s_star)² ≤ 4δ².
  have h_θ_sq_bound : (θ ^ 2 / 2) * (s₂ - s_star) ^ 2 ≤ 4 * (δ : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_right h_one_minus_c_sq (sq_nonneg _)).trans h_final_sq
  -- |s₂ - s_star| ≤ 2√2 · δ / θ, since (s₂ - s_star)² ≤ 8δ²/θ².
  have h_s2_bound : |s₂ - s_star| ≤ 2 * Real.sqrt 2 * δ / θ := by
    have hθ_sq_pos : 0 < θ ^ 2 := pow_pos hθ_pos 2
    have h2 : (s₂ - s_star) ^ 2 ≤ (2 * Real.sqrt 2 * δ / θ) ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
        le_div_iff₀ hθ_sq_pos]
      linarith only [h_θ_sq_bound]
    exact abs_le_of_sq_le_sq h2 (div_nonneg (by positivity) hθ_pos.le)
  -- s := inner ℝ (p - T₂.midpoint) u. |s - s₂| ≤ δ.
  set s : ℝ := (inner ℝ (p - T₂.midpoint) u : ℝ) with hs_def
  have h_s_s2 : |s - s₂| ≤ δ := by
    -- inner (p - T₂.mid - s₂ u) u = s - s₂, so |s - s₂| ≤ ‖p - T₂.mid - s₂ u‖ ≤ δ.
    have h_inner_eq : (inner ℝ (p - T₂.midpoint - s₂ • u) u : ℝ) = s - s₂ := by
      rw [inner_sub_left, inner_smul_left, h_inner_uu, RCLike.conj_to_real, mul_one]
    have h_abs_le : |(inner ℝ (p - T₂.midpoint - s₂ • u) u : ℝ)| ≤
        ‖p - T₂.midpoint - s₂ • u‖ * ‖u‖ :=
      abs_real_inner_le_norm _ _
    rw [hu_norm, mul_one, h_inner_eq] at h_abs_le
    exact h_abs_le.trans hp_T2_norm
  -- Conclude |s - s_star| ≤ δ + 2√2·δ/θ by the triangle inequality.
  exact (abs_sub_le s s₂ s_star).trans (by linarith only [h_s_s2, h_s2_bound])

/-- Slab-containment helper: if every point in `T₁.carrier ∩ T₂.carrier` has its
`T₂`-axis parameter `inner (p - T₂.midpoint) T₂.direction` within distance `L`
of some real `s_star`, then the intersection is contained in the slab cylinder
`cylinder T₂.midpoint T₂.direction (s_star - L) (s_star + L) δ`. -/
lemma inter_subset_cylinder_of_axis_bound
    (hδ : 0 ≤ δ) (T₁ T₂ : Tube δ E) (s_star L : ℝ)
    (h_bound :
      ∀ p ∈ T₁.carrier ∩ T₂.carrier,
        |(inner ℝ (p - T₂.midpoint) T₂.direction : ℝ) - s_star| ≤ L) :
    T₁.carrier ∩ T₂.carrier ⊆
      cylinder T₂.midpoint T₂.direction (s_star - L) (s_star + L) δ := by
  intro p hp
  obtain ⟨hp₁, hp₂⟩ := hp
  have h_axis : |(inner ℝ (p - T₂.midpoint) T₂.direction : ℝ) - s_star| ≤ L :=
    h_bound p ⟨hp₁, hp₂⟩
  have h_axis_le := (abs_le.mp h_axis)
  have h_self : p ∈ cylinder T₂.midpoint T₂.direction (-(1/2) - δ) (1/2 + δ) δ :=
    carrier_subset_cylinder_self T₂ hδ hp₂
  rw [mem_cylinder] at h_self
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · linarith [h_axis_le.1]
  · linarith [h_axis_le.2]
  · exact h_self.2

end

end Tube
