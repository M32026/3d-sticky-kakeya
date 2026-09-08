/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Homothety
public import Kakeya.Tube.BallInTube
public import Kakeya.Tube.CylinderApprox

/-!
# Tube-intersection volume bounds

Pure geometric estimates on the volume of the intersection of two `Tube`s, in
terms of the angle between their directions. These contain no
essential-distinctness content and feed the not-essentially-distinct counting in
`Geo_notEDbound`.

* `volume_inter_le_of_angle` — `vol(T₁ ∩ T₂) ≤ C · δ^(n-1) · min(1, δ/angle)`
  (an upper bound; "Thm 1" of the blueprint).
-/

@[expose] public section

open MeasureTheory
open Topology

namespace Tube

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

omit [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The orthogonal complement of the span of a nonzero vector has dimension one less than the
ambient space. -/
private lemma finrank_orthogonal_span_singleton {d : E} (hd : d ≠ 0) :
    Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E) = Module.finrank ℝ E - 1 := by
  have h1 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (ℝ ∙ d)
  have h2 : Module.finrank ℝ (ℝ ∙ d) = 1 := finrank_span_singleton hd
  omega

/-- Positivity of the `k`-dimensional unit-ball volume constant. -/
private lemma ballConst_pos (k : ℕ) :
    0 < Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1) := by
  positivity -- (extracted by Fuse golfer)

omit [ProperSpace E] in
/-- Volume of a ball centred at the origin of the orthogonal complement of a nonzero vector: the
`(n-1)`-dimensional ball volume, where `n` is the dimension of the ambient space. -/
private lemma volume_closedBall_orthogonal (hn : 1 < Module.finrank ℝ E) {d : E} (hd : d ≠ 0)
    (ρ : ℝ) :
    volume (Metric.closedBall (0 : ((ℝ ∙ d)ᗮ : Submodule ℝ E)) ρ) =
      ENNReal.ofReal ρ ^ (Module.finrank ℝ E - 1) *
        ENNReal.ofReal (Real.sqrt Real.pi ^ (Module.finrank ℝ E - 1) /
          Real.Gamma ((↑(Module.finrank ℝ E - 1) : ℝ) / 2 + 1)) := by
  -- (extracted by Fuse golfer)
  have hfin : Module.finrank ℝ ((ℝ ∙ d)ᗮ : Submodule ℝ E) = Module.finrank ℝ E - 1 :=
    finrank_orthogonal_span_singleton hd
  haveI : Nontrivial ((ℝ ∙ d)ᗮ : Submodule ℝ E) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hfin]; omega)
  rw [InnerProductSpace.volume_closedBall, hfin]

omit [ProperSpace E] in
/-- The volume of a cylinder along a unit direction is finite. -/
private lemma volume_cylinder_ne_top (hn : 1 < Module.finrank ℝ E) {d : E} (hd : ‖d‖ = 1)
    (m : E) (a b r : ℝ) : volume (cylinder m d a b r) ≠ ⊤ := by
  -- (extracted by Fuse golfer)
  rw [volume_cylinder hd, volume_closedBall_orthogonal hn (fun h => by simp [h] at hd)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top)

omit [ProperSpace E] in
/-- Real-valued volume of a cylinder along a unit direction: the axial length times the
`(n-1)`-dimensional ball volume of radius `r`. -/
private lemma measureReal_cylinder (hn : 1 < Module.finrank ℝ E) {d : E} (hd : ‖d‖ = 1)
    (m : E) {a b r : ℝ} (hab : a ≤ b) (hr : 0 ≤ r) :
    volume.real (cylinder m d a b r) =
      (b - a) * r ^ (Module.finrank ℝ E - 1) *
        (Real.sqrt Real.pi ^ (Module.finrank ℝ E - 1) /
          Real.Gamma ((↑(Module.finrank ℝ E - 1) : ℝ) / 2 + 1)) := by
  -- (extracted by Fuse golfer)
  have hC := (ballConst_pos (Module.finrank ℝ E - 1)).le
  rw [measureReal_def, volume_cylinder hd, volume_closedBall_orthogonal hn
      (fun h => by simp [h] at hd), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal hC, mul_assoc]

/-- A `δ`-tube is contained in its own outer cylinder, of axial length `1 + 2δ` and radius `δ`,
so its volume is at most `(1 + 2δ) · δ^(n-1)` times the unit-ball constant. -/
private lemma measureReal_carrier_le (hn : 1 < Module.finrank ℝ E) {δ : NNReal}
    (hδ : (0 : ℝ) ≤ (δ : ℝ)) (T : Tube δ E) :
    volume.real T.carrier ≤ (1 + 2 * (δ : ℝ)) * (δ : ℝ) ^ (Module.finrank ℝ E - 1) *
      (Real.sqrt Real.pi ^ (Module.finrank ℝ E - 1) /
        Real.Gamma ((↑(Module.finrank ℝ E - 1) : ℝ) / 2 + 1)) := by
  -- (extracted by Fuse golfer)
  have h_real := measureReal_mono (μ := volume)
    (_root_.Tube.carrier_subset_cylinder_self T hδ)
    (volume_cylinder_ne_top hn T.norm_direction T.midpoint
      (-(1/2) - (δ : ℝ)) (1/2 + (δ : ℝ)) (δ : ℝ))
  rwa [measureReal_cylinder hn T.norm_direction T.midpoint
      (by linarith only [hδ] : (-(1/2) - (δ : ℝ)) ≤ 1/2 + (δ : ℝ)) hδ,
    show (1/2 + (δ : ℝ)) - (-(1/2) - (δ : ℝ)) = 1 + 2 * (δ : ℝ) from by ring] at h_real

/-- Slab bound for the intersection of two transversal tubes: when the tubes' directions are
closer than their reflections, the intersection is contained in a slab of the second tube's
outer cylinder of axial length `2δ + 4√2·δ/θ`, where `θ = ‖d₁ - d₂‖`. -/
private lemma measureReal_inter_le_slab (hn : 1 < Module.finrank ℝ E) {δ : NNReal} (hδ : 0 < δ)
    (S₁ S₂ : Tube δ E)
    (h_dir_min : ‖S₁.direction - S₂.direction‖ ≤ ‖S₁.direction + S₂.direction‖)
    (h_θ_pos : 0 < ‖S₁.direction - S₂.direction‖) :
    volume.real (S₁.carrier ∩ S₂.carrier) ≤
      (2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / ‖S₁.direction - S₂.direction‖) *
        (Real.sqrt Real.pi ^ (Module.finrank ℝ E - 1) /
          Real.Gamma ((↑(Module.finrank ℝ E - 1) : ℝ) / 2 + 1)) *
        (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
  -- (extracted by Fuse golfer)
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  obtain ⟨s_star, h_bound⟩ :=
    _root_.Tube.exists_axis_param_bound hδ S₁ S₂ h_dir_min h_θ_pos
  set L : ℝ := δ + 2 * Real.sqrt 2 * δ / ‖S₁.direction - S₂.direction‖ with hL_def
  have hS2_dir_norm : ‖S₂.direction‖ = 1 := S₂.norm_direction
  have h_L_nn : 0 ≤ L := by
    rw [hL_def]
    exact add_nonneg hδr.le (div_nonneg
      (mul_nonneg (mul_nonneg zero_le_two (Real.sqrt_nonneg 2)) hδr.le) (norm_nonneg _))
  have h_real_le := measureReal_mono (μ := volume)
    (_root_.Tube.inter_subset_cylinder_of_axis_bound hδ.le S₁ S₂ s_star L h_bound)
    (volume_cylinder_ne_top hn hS2_dir_norm S₂.midpoint (s_star - L) (s_star + L) δ)
  rw [measureReal_cylinder hn hS2_dir_norm S₂.midpoint
      (by linarith only [h_L_nn] : s_star - L ≤ s_star + L) hδr.le,
    show (s_star + L) - (s_star - L) = 2 * δ + 4 * Real.sqrt 2 * δ /
      ‖S₁.direction - S₂.direction‖ from by rw [hL_def]; ring] at h_real_le
  calc volume.real (S₁.carrier ∩ S₂.carrier)
      ≤ (2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / ‖S₁.direction - S₂.direction‖) *
          (δ : ℝ) ^ (Module.finrank ℝ E - 1) *
          (Real.sqrt Real.pi ^ (Module.finrank ℝ E - 1) /
            Real.Gamma ((↑(Module.finrank ℝ E - 1) : ℝ) / 2 + 1)) := h_real_le
    _ = _ := mul_right_comm _ _ _

/-- Symmetric form of the slab bound: the axial length of the containing slab is controlled by
`min ‖d₁ - d₂‖ ‖d₁ + d₂‖`, whichever of the two orientations of the second tube is the closer
one. -/
private lemma measureReal_inter_le_slab_min (hn : 1 < Module.finrank ℝ E) {δ : NNReal}
    (hδ : 0 < δ) (S₁ S₂ : Tube δ E)
    (h_θ_pos : 0 < min ‖S₁.direction - S₂.direction‖ ‖S₁.direction + S₂.direction‖) :
    volume.real (S₁.carrier ∩ S₂.carrier) ≤
      (2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) /
          min ‖S₁.direction - S₂.direction‖ ‖S₁.direction + S₂.direction‖) *
        (Real.sqrt Real.pi ^ (Module.finrank ℝ E - 1) /
          Real.Gamma ((↑(Module.finrank ℝ E - 1) : ℝ) / 2 + 1)) *
        (δ : ℝ) ^ (Module.finrank ℝ E - 1) := by
  have e1 : ‖S₁.direction - S₂.reverse.direction‖ = ‖S₁.direction + S₂.direction‖ := by
    rw [Tube.reverse_direction, sub_neg_eq_add]
  have e2 : ‖S₁.direction + S₂.reverse.direction‖ = ‖S₁.direction - S₂.direction‖ := by
    rw [Tube.reverse_direction, ← sub_eq_add_neg]
  rcases le_total ‖S₁.direction - S₂.direction‖ ‖S₁.direction + S₂.direction‖ with hsa | hsa
  · rw [min_eq_left hsa] at h_θ_pos ⊢
    exact measureReal_inter_le_slab hn hδ S₁ S₂ hsa h_θ_pos
  · rw [min_eq_right hsa] at h_θ_pos ⊢
    have hS := measureReal_inter_le_slab hn hδ S₁ S₂.reverse (by rw [e1, e2]; exact hsa)
      (by rw [e1]; exact h_θ_pos)
    rwa [Tube.reverse_carrier, e1] at hS

/-- The elementary real-arithmetic core shared by the two sub-cases of
`volume_inter_le_of_angle`: for `0 < θ ≤ 2` the slab bound `2δ + 4√2·δ/θ` is dominated by
`(10 + 4√2) · (δ/θ)`. -/
private lemma slab_le_const_mul {V δ θ m : ℝ} (hV : 0 ≤ V) (hδ : 0 < δ) (hθ : 0 < θ)
    (hθ2 : θ ≤ 2) (hm : 0 ≤ m) :
    (2 * δ + 4 * Real.sqrt 2 * δ / θ) * V * m
      ≤ ((7 + 4 * Real.sqrt 2) * V + 3 * V) * m * (δ / θ) := by -- (extracted by Fuse golfer)
  have hd0 : 0 ≤ δ / θ := div_nonneg hδ.le hθ.le
  have h2 : 2 * δ ≤ 4 * (δ / θ) := by
    rw [← mul_div_assoc, le_div_iff₀ hθ]
    linarith [mul_nonneg hδ.le (sub_nonneg.mpr hθ2)]
  have hstep : (2 * δ + 4 * Real.sqrt 2 * (δ / θ)) * V
      ≤ ((7 + 4 * Real.sqrt 2) * V + 3 * V) * (δ / θ) := by
    linarith [mul_nonneg (sub_nonneg.mpr h2) hV, mul_nonneg hd0 hV]
  calc (2 * δ + 4 * Real.sqrt 2 * δ / θ) * V * m
      = (2 * δ + 4 * Real.sqrt 2 * (δ / θ)) * V * m := by rw [mul_div_assoc]
    _ ≤ ((7 + 4 * Real.sqrt 2) * V + 3 * V) * (δ / θ) * m :=
        mul_le_mul_of_nonneg_right hstep hm
    _ = ((7 + 4 * Real.sqrt 2) * V + 3 * V) * m * (δ / θ) := by ring

theorem volume_inter_le_of_angle (hn : 1 < Module.finrank ℝ E) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {δ : NNReal} (_ : 0 < δ) (_ : δ ≤ 1)
        (T₁ T₂ : Tube δ E),
        volume.real (T₁.carrier ∩ T₂.carrier) ≤
          C * δ ^ (Module.finrank ℝ E - 1) *
            min 1 (δ / max (min ‖T₁.direction - T₂.direction‖
                                ‖T₁.direction + T₂.direction‖) δ) := by
  set n := Module.finrank ℝ E with hn_def
  -- Unit ball volume constant in dimension n-1
  set V : ℝ := Real.sqrt Real.pi ^ (n - 1) /
      Real.Gamma (((n - 1 : ℕ) : ℝ) / 2 + 1) with hV_def
  have hV_pos : 0 < V := by rw [hV_def]; exact ballConst_pos _
  -- Define the constant.
  set C : ℝ := (7 + 4 * Real.sqrt 2) * V + 3 * V with hC_def
  have hs2V : (0 : ℝ) ≤ Real.sqrt 2 * V := mul_nonneg (Real.sqrt_nonneg 2) hV_pos.le
  have hC_pos : 0 < C := by rw [hC_def]; linarith only [hV_pos, hs2V]
  refine ⟨C, hC_pos, ?_⟩
  intro δ hδ hδ1 T₁ T₂
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  set θ_sub : ℝ := ‖T₁.direction - T₂.direction‖ with hθ_sub_def
  set θ_add : ℝ := ‖T₁.direction + T₂.direction‖ with hθ_add_def
  set θ_min : ℝ := min θ_sub θ_add with hθ_min_def
  set fac : ℝ := min 1 (δ / max θ_min δ) with hfac_def
  -- Establish: ‖T_i.direction‖ = 1
  have hd1_norm : ‖T₁.direction‖ = 1 := T₁.norm_direction
  have hd2_norm : ‖T₂.direction‖ = 1 := T₂.norm_direction
  have hδpow_nn : 0 ≤ δ ^ (n - 1) := pow_nonneg hδ.le _
  -- Outer-cylinder bound on the intersection
  have h_inter_le_outer :
      volume.real (T₁.carrier ∩ T₂.carrier) ≤ 3 * V * δ ^ (n - 1) := by
    have h_real_le := measureReal_carrier_le hn hδr.le T₂
    rw [← hn_def, ← hV_def] at h_real_le
    refine (measureReal_mono Set.inter_subset_right
      T₂.isCompact.measure_lt_top.ne).trans (h_real_le.trans ?_)
    linarith only [mul_nonneg (sub_nonneg.mpr (NNReal.coe_le_one.mpr hδ1))
      (mul_nonneg (pow_nonneg hδr.le (n - 1)) hV_pos.le)]
  -- Now case-split on which of θ_sub, θ_add is the minimum.
  by_cases h_le_δ : θ_min ≤ δ
  · -- Regime A: θ_min ≤ δ. Then max θ_min δ = δ, so fac = 1.
    rw [hfac_def, max_eq_right h_le_δ, div_self hδr.ne', min_self, mul_one]
    refine h_inter_le_outer.trans (mul_le_mul_of_nonneg_right ?_ hδpow_nn)
    rw [hC_def]; linarith only [hV_pos, hs2V]
  · -- Regime B: θ_min > δ. So max θ_min δ = θ_min, fac = δ/θ_min.
    push Not at h_le_δ
    have hθ_min_pos : 0 < θ_min := lt_trans hδ h_le_δ
    -- Bound 2: θ_min ≤ θ_sub ≤ ‖d1‖ + ‖d2‖ = 2
    have hθ_min_le_2 : θ_min ≤ 2 := by
      rw [hθ_min_def, hθ_sub_def]
      refine (min_le_left _ _).trans ?_
      have h := norm_sub_le T₁.direction T₂.direction
      rw [hd1_norm, hd2_norm] at h
      linarith only [h]
    rw [hfac_def, max_eq_left h_le_δ.le,
      min_eq_right ((div_le_one hθ_min_pos).mpr h_le_δ.le), hC_def]
    refine (measureReal_inter_le_slab_min hn hδ T₁ T₂
      (by rw [← hθ_sub_def, ← hθ_add_def, ← hθ_min_def]; exact hθ_min_pos)).trans ?_
    rw [← hn_def, ← hV_def, ← hθ_sub_def, ← hθ_add_def, ← hθ_min_def]
    exact slab_le_const_mul hV_pos.le hδr hθ_min_pos hθ_min_le_2 hδpow_nn

/-- The volume of a closed ball of radius `r` in a finite-dimensional real inner
product space is at most `(2r)^(dim)`, since the ball lies in the cube `[-r,r]^dim`. -/
lemma volume_closedBall_le_cube {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : F) r) ≤ ENNReal.ofReal ((2 * r) ^ (Module.finrank ℝ F)) := by
  rw [Measure.addHaar_closedBall' volume (0 : F) hr]
  calc
    ENNReal.ofReal (r ^ Module.finrank ℝ F) * volume (Metric.closedBall (0 : F) 1)
        ≤ ENNReal.ofReal (r ^ Module.finrank ℝ F) * 2 ^ Module.finrank ℝ F := by
          gcongr
          exact volume_closedBall_le_two_pow_finrank (E := F)
    _ = ENNReal.ofReal ((2 * r) ^ Module.finrank ℝ F) := by
      rw [ENNReal.ofReal_pow hr, ← mul_pow,
        ENNReal.ofReal_pow (mul_nonneg (by positivity) hr),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
      norm_num [mul_comm]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- For unit vectors `u, u'`, `√(1 - ⟨u,u'⟩²) ≤ min ‖u - u'‖ ‖u + u'‖`. -/
lemma sin_le_min_norm {u u' : E} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1) :
    Real.sqrt (1 - (inner ℝ u u') ^ 2) ≤ min ‖u - u'‖ ‖u + u'‖ := by
  refine le_min ((Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (norm_nonneg _)))
    ((Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq (norm_nonneg _)))
  · rw [norm_sub_sq_real, hu, hu']; linarith [sq_nonneg (1 - inner ℝ u u')]
  · rw [norm_add_sq_real, hu, hu']; linarith [sq_nonneg (1 + inner ℝ u u')]

/-- Cube cross-section version of the slab bound (`key_slab` with a cube cross-section): when
`‖S₁.dir - S₂.dir‖ ≤ ‖S₁.dir + S₂.dir‖` is positive, the intersection lies in a slab cylinder of
axial length `2δ + 4√2·δ/‖S₁.dir - S₂.dir‖` and cube cross-section `(2δ)^(n-1)`. -/
lemma volume_inter_le_slab_cube {δ : NNReal} (hδ : 0 < δ) (S₁ S₂ : Tube δ E)
    (h_dir_min : ‖S₁.direction - S₂.direction‖ ≤ ‖S₁.direction + S₂.direction‖)
    (h_θ_pos : 0 < ‖S₁.direction - S₂.direction‖) :
    volume.real (S₁.carrier ∩ S₂.carrier) ≤
      (2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / ‖S₁.direction - S₂.direction‖)
        * (2 * (δ : ℝ)) ^ (Module.finrank ℝ E - 1) := by
  set n := Module.finrank ℝ E with hn_def
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  obtain ⟨s_star, h_bound⟩ :=
    _root_.Tube.exists_axis_param_bound hδ S₁ S₂ h_dir_min h_θ_pos
  set L : ℝ := δ + 2 * Real.sqrt 2 * δ / ‖S₁.direction - S₂.direction‖ with hL_def
  have hS2_dir_norm : ‖S₂.direction‖ = 1 := S₂.norm_direction
  have hd_ne : S₂.direction ≠ 0 := by
    rw [← norm_ne_zero_iff, hS2_dir_norm]; exact one_ne_zero
  have h_ball_cube :
      volume (Metric.closedBall (0 : ((ℝ ∙ S₂.direction)ᗮ : Submodule ℝ E)) (δ : ℝ))
        ≤ ENNReal.ofReal ((2 * (δ : ℝ)) ^ (n - 1)) := by
    have h := volume_closedBall_le_cube (F := ((ℝ ∙ S₂.direction)ᗮ : Submodule ℝ E)) (δ : ℝ) hδr.le
    rwa [finrank_orthogonal_span_singleton hd_ne] at h
  have h_L_nn : 0 ≤ L := by rw [hL_def]; positivity
  have h_inter_le : volume (S₁.carrier ∩ S₂.carrier) ≤
      ENNReal.ofReal (2 * L) * ENNReal.ofReal ((2 * (δ : ℝ)) ^ (n - 1)) := by
    calc volume (S₁.carrier ∩ S₂.carrier)
        ≤ volume (cylinder S₂.midpoint S₂.direction (s_star - L) (s_star + L) δ) :=
          measure_mono
            (_root_.Tube.inter_subset_cylinder_of_axis_bound hδ.le S₁ S₂ s_star L h_bound)
      _ = ENNReal.ofReal ((s_star + L) - (s_star - L)) *
            volume (Metric.closedBall (0 : ((ℝ ∙ S₂.direction)ᗮ : Submodule ℝ E)) (δ : ℝ)) :=
          volume_cylinder (d := S₂.direction) hS2_dir_norm S₂.midpoint
            (s_star - L) (s_star + L) δ
      _ ≤ ENNReal.ofReal (2 * L) * ENNReal.ofReal ((2 * (δ : ℝ)) ^ (n - 1)) := by
          rw [show (s_star + L) - (s_star - L) = 2 * L from by ring]
          exact mul_le_mul_right h_ball_cube _
  have hmono := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h_inter_le
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith only [h_L_nn] : (0 : ℝ) ≤ 2 * L),
    ENNReal.toReal_ofReal (pow_nonneg (by linarith only [hδr.le]) (n - 1)),
    show 2 * L = 2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / ‖S₁.direction - S₂.direction‖ from by
      rw [hL_def]; ring] at hmono

/-- **Gram-determinant transversality bound** (real-valued form, "Thm 1" packaged with the sine
factor): for `δ`-tubes `T, T'` with `0 < δ ≤ 1`,
`√(1 - ⟨T.dir, T'.dir⟩²) · vol(T ∩ T') ≤ 4^n · δ^n`. When the directions are (anti)parallel the
left side vanishes; otherwise the ambient dimension is at least `2`, and a single transverse slab
plus the cube cross-section bound give the estimate. -/
theorem volume_inter_mul_sin_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (T T' : Tube δ E) :
    Real.sqrt (1 - (inner ℝ T.direction T'.direction) ^ 2) *
        volume.real (T.carrier ∩ T'.carrier)
      ≤ 4 ^ (Module.finrank ℝ E) * (δ : ℝ) ^ (Module.finrank ℝ E) := by
  set n := Module.finrank ℝ E with hn_def
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  set u : E := T.direction with hu_def
  set u' : E := T'.direction with hu'_def
  have hu_norm : ‖u‖ = 1 := T.norm_direction
  have hu_ne : u ≠ 0 := by rw [← norm_ne_zero_iff, hu_norm]; norm_num
  haveI : Nontrivial E := ⟨⟨u, 0, hu_ne⟩⟩
  have hu'_norm : ‖u'‖ = 1 := T'.norm_direction
  set c : ℝ := inner ℝ u u' with hc
  set s : ℝ := Real.sqrt (1 - c ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hvol_nn : 0 ≤ volume.real (T.carrier ∩ T'.carrier) := measureReal_nonneg
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · rw [← hs_eq, zero_mul]; positivity
  -- `s > 0`: directions are independent, so `n ≥ 2`.
  have hc_sq_lt : c ^ 2 < 1 := by
    rw [hs] at hs_pos
    linarith only [Real.sqrt_pos.mp hs_pos]
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hpos : 0 < n := by rw [hn_def]; exact Module.finrank_pos
    have htop : (ℝ ∙ u) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [finrank_span_singleton hu_ne]; omega)
    obtain ⟨r, hr⟩ :=
      Submodule.mem_span_singleton.mp (Submodule.eq_top_iff'.mp htop u')
    have habs : |r| = 1 := by
      rw [← hu'_norm, ← hr, norm_smul, Real.norm_eq_abs, hu_norm, mul_one]
    rw [hc, ← hr, real_inner_smul_right, real_inner_self_eq_norm_sq, hu_norm, one_pow,
      mul_one, ← sq_abs, habs] at hc_sq_lt
    norm_num at hc_sq_lt
  -- Sine bounds and power identities.
  have hsin_min : s ≤ min ‖u - u'‖ ‖u + u'‖ := sin_le_min_norm hu_norm hu'_norm
  have hs_le_1 : s ≤ 1 := by rw [hs, Real.sqrt_le_one]; linarith only [sq_nonneg c]
  have hP2 : (2 : ℝ) ≤ 2 ^ (n - 1) := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ n - 1 by omega)
  have hP0 : (0 : ℝ) < 2 ^ (n - 1) := pow_pos (by norm_num) _
  have hQ0 : (0 : ℝ) ≤ (δ : ℝ) ^ (n - 1) := pow_nonneg hδr.le _
  have hpow_two : (2 * (δ : ℝ)) ^ (n - 1) = 2 ^ (n - 1) * (δ : ℝ) ^ (n - 1) :=
    mul_pow 2 (δ : ℝ) (n - 1)
  have hδn : (δ : ℝ) ^ n = (δ : ℝ) ^ (n - 1) * (δ : ℝ) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  have h4n : (4 : ℝ) ^ n = 2 ^ (n - 1) * 2 ^ (n - 1) * 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show 2 * n = (n - 1) + (n - 1) + 2 from by omega, pow_add, pow_add]
  by_cases hθδ : min ‖u - u'‖ ‖u + u'‖ ≤ (δ : ℝ)
  · -- Region A: nearly transverse (angle `≳ δ`); use the whole-tube volume bound.
    have hs_le_δ : s ≤ (δ : ℝ) := le_trans hsin_min hθδ
    have h_vol_le : volume.real (T.carrier ∩ T'.carrier) ≤
        (2 : ℝ) ^ (n + 1) * (δ : ℝ) ^ (n - 1) := by
      calc volume.real (T.carrier ∩ T'.carrier)
          ≤ volume.real T'.carrier :=
            measureReal_mono Set.inter_subset_right T'.isCompact.measure_lt_top.ne
        _ ≤ (2 : ℝ) ^ (n + 1) * (δ : ℝ) ^ (n - 1) := by
          simpa only [measureReal_def, Tube.volume_le.C, hn_def, ENNReal.toReal_mul,
            ENNReal.coe_toReal, ENNReal.toReal_pow, NNReal.coe_pow, NNReal.coe_ofNat] using
            ENNReal.toReal_mono
              (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))
              (Tube.volume_le hδ1 T')
    have hC : (2 : ℝ) ^ (n + 1) ≤ 4 ^ n := by
      rw [show (4 : ℝ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc s * volume.real (T.carrier ∩ T'.carrier)
        ≤ (δ : ℝ) * ((2 : ℝ) ^ (n + 1) * (δ : ℝ) ^ (n - 1)) :=
          mul_le_mul hs_le_δ h_vol_le hvol_nn hδr.le
      _ = (2 : ℝ) ^ (n + 1) * ((δ : ℝ) ^ (n - 1) * (δ : ℝ)) := by ring
      _ ≤ 4 ^ n * ((δ : ℝ) ^ (n - 1) * (δ : ℝ)) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg hQ0 hδr.le)
      _ = 4 ^ n * (δ : ℝ) ^ n := by rw [hδn]
  · -- Region B: nearly parallel (angle `< δ`); use the transverse-slab bound.
    push Not at hθδ
    have hθ_min_pos : 0 < min ‖u - u'‖ ‖u + u'‖ := lt_trans hδr hθδ
    have h_vol_le : volume.real (T.carrier ∩ T'.carrier) ≤
        (2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / min ‖u - u'‖ ‖u + u'‖) *
          (2 * (δ : ℝ)) ^ (n - 1) := by
      by_cases hsub_le_add : ‖u - u'‖ ≤ ‖u + u'‖
      · rw [min_eq_left hsub_le_add] at hθ_min_pos ⊢
        exact volume_inter_le_slab_cube hδ T T' hsub_le_add hθ_min_pos
      · push Not at hsub_le_add
        rw [min_eq_right hsub_le_add.le] at hθ_min_pos ⊢
        have h_sub_eq : ‖T.direction - T'.reverse.direction‖ = ‖u + u'‖ := by
          rw [Tube.reverse_direction, hu_def, hu'_def, sub_neg_eq_add]
        have h_add_eq : ‖T.direction + T'.reverse.direction‖ = ‖u - u'‖ := by
          rw [Tube.reverse_direction, hu_def, hu'_def, ← sub_eq_add_neg]
        have hSlab := volume_inter_le_slab_cube hδ T T'.reverse
          (by rw [h_sub_eq, h_add_eq]; exact hsub_le_add.le) (by rw [h_sub_eq]; exact hθ_min_pos)
        rwa [Tube.reverse_carrier, h_sub_eq] at hSlab
    -- `s · (2δ + 4√2·δ/θ) ≤ 8δ`, using `s ≤ 1` and `s ≤ θ`.
    have hsqrt2_lt : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    have h_factor : s * (2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / min ‖u - u'‖ ‖u + u'‖)
        ≤ 8 * (δ : ℝ) := by
      have h1 : s * (2 * (δ : ℝ)) ≤ 2 * (δ : ℝ) :=
        mul_le_of_le_one_left (by linarith only [hδr.le]) hs_le_1
      have h2 : s * (4 * Real.sqrt 2 * (δ : ℝ) / min ‖u - u'‖ ‖u + u'‖)
          ≤ 4 * Real.sqrt 2 * (δ : ℝ) := by
        rw [mul_div_assoc', div_le_iff₀ hθ_min_pos]
        linarith only [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt 2 * (δ : ℝ))
          (sub_nonneg.mpr hsin_min)]
      linarith only [h1, h2, mul_lt_mul_of_pos_right hsqrt2_lt hδr]
    calc s * volume.real (T.carrier ∩ T'.carrier)
        ≤ s * ((2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / min ‖u - u'‖ ‖u + u'‖) *
            (2 * (δ : ℝ)) ^ (n - 1)) := mul_le_mul_of_nonneg_left h_vol_le hs0
      _ = (s * (2 * (δ : ℝ) + 4 * Real.sqrt 2 * (δ : ℝ) / min ‖u - u'‖ ‖u + u'‖)) *
            (2 * (δ : ℝ)) ^ (n - 1) := by ring
      _ ≤ 8 * (δ : ℝ) * (2 * (δ : ℝ)) ^ (n - 1) :=
            mul_le_mul_of_nonneg_right h_factor (pow_nonneg (by linarith only [hδr.le]) _)
      _ ≤ 4 ^ n * (δ : ℝ) ^ n := by
          rw [hpow_two, h4n, hδn]
          linarith only [mul_nonneg (mul_nonneg (mul_nonneg hP0.le hQ0) hδr.le)
            (by linarith only [hP2] : (0 : ℝ) ≤ 2 ^ (n - 1) - 2)]

/-- Bernoulli bound for the sliding constant: for `n ≥ 2` the `(n-1)`-st power of
`1 - 2/(8n)` stays above `3/4`. -/
private lemma three_quarters_le_pow_one_sub {n : ℕ} (hn : 2 ≤ n) :
    (3 : ℝ) / 4 ≤ (1 - 2 * (1 / (8 * (n : ℝ)))) ^ (n - 1) := by
  -- (extracted by Fuse golfer)
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set c : ℝ := 1 / (8 * (n : ℝ)) with hc_def
  have hc0 : 0 ≤ c := by rw [hc_def]; exact div_nonneg zero_le_one (by linarith only [hnR])
  have hc16 : c ≤ 1 / 16 := by
    rw [hc_def]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hnR])
  have hcn : c * (n : ℝ) = 1 / 8 := by
    rw [hc_def, one_div, mul_inv, mul_assoc,
      inv_mul_cancel₀ (ne_of_gt (by linarith only [hnR] : (0 : ℝ) < (n : ℝ))), mul_one, ← one_div]
  have h := one_add_mul_le_pow (by linarith only [hc16] : (-2 : ℝ) ≤ -(2 * c)) (n - 1)
  rw [← sub_eq_add_neg, Nat.cast_sub (Nat.le_of_succ_le hn), Nat.cast_one] at h
  linarith only [h, hcn, hc0]

/-- **Nearly-parallel sliding** ("Thm 4" of the blueprint): two `δ`-tubes that are
nearly parallel and whose midpoints satisfy a small-perpendicular + bounded-parallel
constraint overlap in more than half of `max(vol T₁, vol T₂)`, hence are *not*
essentially distinct. -/
theorem nearly_parallel_sliding (hn : 1 < Module.finrank ℝ E) :
    ∃ (c_slide κ δ₀ : ℝ), 0 < c_slide ∧ 0 < κ ∧ κ < 1 / 2 ∧
      0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_ : 0 < δ) (_ : (δ : ℝ) ≤ δ₀)
        (T₁ T₂ : Tube δ E),
        min ‖T₁.direction - T₂.direction‖
            ‖T₁.direction + T₂.direction‖ ≤ c_slide * (δ : ℝ) →
        ‖T₁.midpoint - T₂.midpoint -
          (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) •
            T₂.direction‖ ≤ c_slide * (δ : ℝ) →
        |inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction| ≤ 1 / 2 - κ →
        ¬ IsEssentiallyDistinct T₁.carrier T₂.carrier := by
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn2 : 2 ≤ n := hn
  have hn2R : 2 ≤ (n : ℝ) := by exact_mod_cast hn2
  have hc_pos : (0 : ℝ) < 1 / (8 * (n : ℝ)) := div_pos one_pos (by linarith only [hn2R])
  have hc_le_half : 1 / (8 * (n : ℝ)) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ (by linarith only [hn2R]) (by norm_num)]; linarith only [hn2R]
  refine ⟨1 / (8 * (n : ℝ)), 1 / 4, 1 / 32, hc_pos, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_⟩
  intro δ hδ hδ_le T₁ T₂ h_dir_min h_perp h_t_bound
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  set c_slide : ℝ := 1 / (8 * (n : ℝ)) with hc_slide_def
  have hc_nn : (0 : ℝ) ≤ c_slide := hc_pos.le
  have h_one_minus_2c_pos : 0 < 1 - 2 * c_slide := by linarith only [hc_le_half]
  -- WLOG reduce to the case ‖T₁.dir - T₂.dir‖ ≤ c_slide * δ.
  suffices h_main : ∀ (T₁ T₂ : Tube δ E),
      ‖T₁.direction - T₂.direction‖ ≤ c_slide * (δ : ℝ) →
      ‖T₁.midpoint - T₂.midpoint -
        (inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction) • T₂.direction‖
          ≤ c_slide * (δ : ℝ) →
      |inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction| ≤ 1 / 4 →
      ¬ IsEssentiallyDistinct T₁.carrier T₂.carrier by
    have h_t' : |inner ℝ (T₁.midpoint - T₂.midpoint) T₂.direction| ≤ 1 / 4 := by
      linarith only [h_t_bound]
    rcases min_le_iff.mp h_dir_min with h_minus | h_plus
    · exact h_main T₁ T₂ h_minus h_perp h_t'
    · -- Use T₁.reverse instead.
      have h_rev := h_main T₁.reverse T₂
        (by rwa [Tube.reverse_direction, show -T₁.direction - T₂.direction
              = -(T₁.direction + T₂.direction) from by abel, norm_neg])
        (by rwa [Tube.reverse_midpoint])
        (by rwa [Tube.reverse_midpoint])
      rwa [Tube.reverse_carrier] at h_rev
  -- Main step.
  clear h_dir_min h_perp h_t_bound
  rintro T₁ T₂ h_dir h_perp h_t_bound h_ED
  set u : E := T₂.direction with hu_def
  set Δm : E := T₁.midpoint - T₂.midpoint with hΔm_def
  set t : ℝ := (inner ℝ Δm u : ℝ) with ht_def
  have hu_norm : ‖u‖ = 1 := T₂.norm_direction
  obtain ⟨ht_lb, ht_ub⟩ := abs_le.mp h_t_bound
  -- Set up cylinder parameters.
  set a : ℝ := max (-(1 / 2 : ℝ)) (t - 1 / 2) with ha_def
  set b : ℝ := min (1 / 2 : ℝ) (t + 1 / 2) with hb_def
  set r : ℝ := (1 - 2 * c_slide) * (δ : ℝ) with hr_def
  have hr_pos : 0 < r := mul_pos h_one_minus_2c_pos hδr
  have hr_le_δ : r ≤ (δ : ℝ) := by rw [hr_def]; linarith only [mul_nonneg hc_nn hδr.le]
  have h_ha_lb : -(1 / 2 : ℝ) ≤ a := le_max_left _ _
  have h_hb_ub : b ≤ 1 / 2 := min_le_left _ _
  have h_b_minus_a_ge : (3 : ℝ) / 4 ≤ b - a := by
    rw [ha_def, hb_def, min_def, max_def]; split_ifs <;> linarith only [ht_lb, ht_ub]
  -- The cylinder.
  set cyl : Set E := cylinder T₂.midpoint u a b r with hcyl_def
  have h_cyl_in_T2 : cyl ⊆ T₂.carrier :=
    _root_.Tube.cylinder_subset_carrier_self T₂ h_ha_lb h_hb_ub hr_le_δ
  have h_cyl_in_T1 : cyl ⊆ T₁.carrier :=
    _root_.Tube.cylinder_T2_subset_T1_carrier hδ hc_nn h_dir h_perp
      (le_max_right _ _) (min_le_right _ _) hr_def.le
  have h_cyl_subset : cyl ⊆ T₁.carrier ∩ T₂.carrier := fun p hp =>
    ⟨h_cyl_in_T1 hp, h_cyl_in_T2 hp⟩
  -- Volume computation.
  have hb_a_nn : 0 ≤ b - a := by linarith only [h_b_minus_a_ge]
  have hab_le : a ≤ b := sub_nonneg.mp hb_a_nn
  set Cn1 : ℝ := Real.sqrt Real.pi ^ (n - 1) / Real.Gamma ((↑(n - 1) : ℝ) / 2 + 1)
    with hCn1_def
  have hCn1_pos : 0 < Cn1 := by rw [hCn1_def]; exact ballConst_pos _
  have h_cyl_real : volume.real cyl = (b - a) * r ^ (n - 1) * Cn1 := by
    rw [hcyl_def, measureReal_cylinder hn hu_norm _ hab_le hr_pos.le, ← hn_def, ← hCn1_def]
  -- Now convert to real.
  set X : ℝ := (δ : ℝ) ^ (n - 1) * Cn1 with hX_def
  have hX_pos : 0 < X := by rw [hX_def]; exact mul_pos (pow_pos hδr _) hCn1_pos
  have h_vol_cyl_real_lb : volume.real cyl ≥ (b - a) * (1 - 2 * c_slide) ^ (n - 1) * X := by
    rw [h_cyl_real, hX_def, hr_def, mul_pow]; exact le_of_eq (by ring)
  -- Finiteness of carriers.
  have hT1_fin : volume T₁.carrier ≠ ⊤ := T₁.isCompact.measure_lt_top.ne
  have hT2_fin : volume T₂.carrier ≠ ⊤ := T₂.isCompact.measure_lt_top.ne
  have h_max_le : max (volume.real T₁.carrier) (volume.real T₂.carrier) ≤
      (1 + 2 * (δ : ℝ)) * (δ : ℝ) ^ (n - 1) * Cn1 :=
    max_le (measureReal_carrier_le hn hδr.le T₁) (measureReal_carrier_le hn hδr.le T₂)
  have h_cyl_le_inter : volume.real cyl ≤ volume.real (T₁.carrier ∩ T₂.carrier) :=
    measureReal_mono (μ := volume) h_cyl_subset
      (lt_of_le_of_lt (measure_mono Set.inter_subset_left) T₁.isCompact.measure_lt_top).ne
  -- Combine. Convert h_ED from ENNReal form to ℝ form.
  have h_inter_le : volume.real (T₁.carrier ∩ T₂.carrier) ≤
      (1/2 : ℝ) * max (volume.real T₁.carrier) (volume.real T₂.carrier) := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ⊤)
        (by rw [ne_eq, max_eq_top, not_or]; exact ⟨hT1_fin, hT2_fin⟩))
      (h_ED : volume (T₁.carrier ∩ T₂.carrier) ≤
        (1 / 2 : ENNReal) * max (volume T₁.carrier) (volume T₂.carrier))
    rwa [ENNReal.toReal_mul, show ((1 / 2 : ENNReal).toReal : ℝ) = 1 / 2 by simp,
      ENNReal.toReal_max hT1_fin hT2_fin] at h
  -- Combine with lower bound.
  have h_reduced : (b - a) * (1 - 2 * c_slide) ^ (n - 1) ≤ (1/2) * (1 + 2 * (δ : ℝ)) := by
    refine le_of_mul_le_mul_right ?_ hX_pos
    calc (b - a) * (1 - 2 * c_slide) ^ (n - 1) * X
        ≤ (1/2 : ℝ) * ((1 + 2 * (δ : ℝ)) * (δ : ℝ) ^ (n - 1) * Cn1) :=
          le_trans h_vol_cyl_real_lb (h_cyl_le_inter.trans
            (h_inter_le.trans (mul_le_mul_of_nonneg_left h_max_le (by norm_num))))
      _ = (1/2) * (1 + 2 * (δ : ℝ)) * X := by rw [hX_def]; ring
  -- Bernoulli: (1 - 2*c_slide)^(n - 1) ≥ 3/4.
  have h_bern_lb : (3 : ℝ) / 4 ≤ (1 - 2 * c_slide) ^ (n - 1) :=
    three_quarters_le_pow_one_sub hn2
  -- (b-a) * (1 - 2c)^(n-1) ≥ (3/4) * (3/4) = 9/16 > 17/32 ≥ (1/2) * (1 + 2δ)
  linarith only [h_reduced, hδ_le,
    mul_le_mul h_b_minus_a_ge h_bern_lb (by norm_num : (0:ℝ) ≤ 3 / 4) hb_a_nn]

end

end Tube

/- Reduction-specific tube geometry: the dilate of a tube, the Gram-determinant
transversality bound, and the "heavy overlap ⇒ containment in a dilate" chain used by
`Kakeya.Tube.refineToEssDistinctLeaves`. -/
namespace Kakeya

noncomputable section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Four-term triangle inequality, used for the telescoping decompositions in
`Tube.tubeOverlapCoreClose`. -/
private lemma norm_add₄_le {F : Type*} [SeminormedAddCommGroup F] (a b c d : F) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := -- (extracted by Fuse golfer)
  (norm_add_le _ _).trans (by linarith [norm_add_le (a + b) c, norm_add_le a b])

/-- (blueprint `def:tubeDilateVolume_constant`) The factor
`C_{\ref{lem:tubeDilateVolume}}' = C ^ n` by which an affine homothety of ratio `C` multiplies
`n`-dimensional volume. For a fixed factor `C > 1` it depends only on the ambient dimension `n`. -/
noncomputable abbrev Tube.tubeDilateVolume.C' (n : ℕ) (C : ℝ) : ℝ := C ^ n

/-- The dilate `C · T` of a `δ`-tube about its center by a factor `C`: the image of `T` under the
affine homothety of ratio `C` centred at `T.center`, realised as a convex body. -/
noncomputable def Tube.dilate {δ : NNReal} (T : Tube δ E) (C : ℝ) : ConvexSpaceBody E :=
  ConvexSpaceBody.affineImage (AffineMap.homothety T.center C)
    (AffineMap.homothety_continuous T.center C) T.toConvexSpaceBody

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- The carrier of the `C`-dilate of `T` is the homothety image of `T`'s carrier. -/
lemma Tube.dilate_carrier {δ : NNReal} (T : Tube δ E) (C : ℝ) :
    (Tube.dilate T C).carrier = AffineMap.homothety T.center C '' T.carrier := by
  rw [Tube.dilate]; simp -- (extracted by Fuse golfer)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The image of a closed ball under a homothety of positive ratio.** -/
lemma image_homothety_closedBall (o : E) {c : ℝ} (hc : 0 < c) (z : E) (r : ℝ) :
    AffineMap.homothety o c '' Metric.closedBall z r
      = Metric.closedBall (AffineMap.homothety o c z) (c * r) := by
  refine Set.Subset.antisymm ?_ ?_
  · -- every point of the image has distance `≤ c * r` from the dilated centre
    intro w hw
    rcases hw with ⟨v, hv, rfl⟩
    rw [Metric.mem_closedBall]
    rw [Kakeya.dist_homothety_homothety o c v z, abs_of_pos hc]
    have hvdist : dist v z ≤ r := by
      rwa [Metric.mem_closedBall] at hv
    exact mul_le_mul_of_nonneg_left hvdist hc.le
  · -- every point of the target ball is a dilated image
    intro w hw
    have hwdist : dist w (AffineMap.homothety o c z) ≤ c * r := by
      simpa [dist_comm] using (Metric.mem_closedBall.mp hw)
    have hz : z = AffineMap.homothety o c⁻¹ (AffineMap.homothety o c z) := by
      rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul,
        inv_mul_cancel₀ hc.ne', one_smul, sub_add_cancel]
    refine ⟨AffineMap.homothety o c⁻¹ w, ?_, ?_⟩
    · -- the preimage lies in the original ball
      rw [Metric.mem_closedBall, hz]
      rw [Kakeya.dist_homothety_homothety o c⁻¹ w (AffineMap.homothety o c z)]
      rw [abs_of_pos (inv_pos.mpr hc)]
      calc
        c⁻¹ * dist w (AffineMap.homothety o c z) ≤ c⁻¹ * (c * r) :=
          mul_le_mul_of_nonneg_left hwdist (inv_pos.mpr hc).le
        _ = r := by rw [inv_mul_cancel_left₀ hc.ne']
    · -- applying the original homothety to the preimage recovers `w`
      rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul,
        mul_inv_cancel₀ hc.ne', one_smul, sub_add_cancel]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Capsule form of a tube dilate.** For a ratio `c > 0`, the `c`-dilate of a `δ`-tube `T` is
the closed `c * δ`-neighbourhood of the segment joining the dilated endpoints; that is, it is
again a capsule, of core length `c` and radius `c * δ`.

This is the form in which `Tube.dilate` is fed to the capsule lemmas
`Kakeya.exists_ball_subset_cthickening_inter_ball` and
`Kakeya.volume_cthickening_le_mul_volume_inter_cthickening`. -/
lemma Tube.dilate_carrier_eq_cthickening {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 0 < c) :
    (Tube.dilate T c).carrier =
      Metric.cthickening (c * (δ : ℝ))
        (segment ℝ (AffineMap.homothety T.center c T.x)
          (AffineMap.homothety T.center c T.y)) := by
  rw [Tube.dilate_carrier, T.carrier_eq]
  rw [Set.image_iUnion₂]
  simp_rw [image_homothety_closedBall T.center hc]
  rw [← Set.biUnion_image (s := segment ℝ T.x T.y)
    (f := AffineMap.homothety T.center c)
    (g := fun w : E => Metric.closedBall w (c * (δ : ℝ)))]
  rw [image_segment]
  rw [← isCompact_segment.cthickening_eq_biUnion_closedBall
    (mul_nonneg hc.le (NNReal.coe_nonneg δ))]

omit [Nontrivial E] in
/-- (blueprint `lem:tubeDilateVolume`) Volume of a tube dilate. For a `δ`-tube `T` and a factor
`C > 1`, the dilate `C · T` — the homothety of `T` about its center by `C`, which is a convex body
by construction of `Tube.dilate` — satisfies `|C · T| = C ^ n · |T|`. -/
theorem Tube.tubeDilateVolume {δ : NNReal} (T : Tube δ E) {C : ℝ} (hC : 1 < C) :
    volume (Tube.dilate T C).carrier
      = ENNReal.ofReal (Tube.tubeDilateVolume.C' (Module.finrank ℝ E) C) * volume T.carrier := by
  rw [Tube.dilate_carrier, MeasureTheory.Measure.addHaar_image_homothety,
    abs_of_pos (pow_pos (zero_lt_one.trans hC) (Module.finrank ℝ E))]

/-- (blueprint `def:tubeOverlapTransversal_constant`) The dimensional constant
`C_{\ref{lem:tubeOverlapTransversal}} = 4^n` in the Gram-determinant transversality bound
`√(det G) |T ∩ T'| ≤ C_n δ^n`. -/
noncomputable def Tube.overlapTransversal.C (n : ℕ) : ℝ := 4 ^ n

omit [Nontrivial E] in
/-- **Measure-theoretic core of the transversality bound** (real-valued form): for `0 < δ ≤ 1`,
`√(1 − ⟨u,u'⟩²) · |T ∩ T'| ≤ 4^n · δ^n`, with `|T ∩ T'|` the real-valued volume. This repackages
the geometric estimate `Tube.volume_inter_mul_sin_le`, whose proof intersects `T` with one
transverse slab from `T'` and controls the cross-section by a cube. -/
private theorem Tube.overlapTransversal_toReal {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T T' : Tube δ E) :
    Real.sqrt (1 - (inner ℝ T.direction T'.direction) ^ 2)
        * (volume (T.carrier ∩ T'.carrier)).toReal
      ≤ Tube.overlapTransversal.C (Module.finrank ℝ E) * (δ : ℝ) ^ (Module.finrank ℝ E) :=
  Tube.volume_inter_mul_sin_le hδ hδ1 T T'

omit [Nontrivial E] in
/-- (blueprint `lem:tubeOverlapTransversal`) Gram-determinant transversality bound.
If `T, T'` are δ-tubes in ℝ^n (with `0 < δ ≤ 1`) with unit core directions `u := T.direction`,
`u' := T'.direction`, then `sin θ · |T ∩ T'| ≤ 4^n · δ^n` where `θ` is the angle between `u` and
`u'`, equivalently `√(1 − ⟨u, u'⟩²) · |T ∩ T'| ≤ 4^n · δ^n`. The bound is translation-invariant and
vacuous when `u = ±u'` (det G = 0).

The proof packages the real-valued core `Tube.overlapTransversal_toReal` (which in turn rests on
`Tube.volume_inter_mul_sin_le`) into the `ENNReal` statement used downstream. -/
theorem Tube.overlapTransversal {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (T T' : Tube δ E) :
    ENNReal.ofReal (Real.sqrt (1 - (inner ℝ T.direction T'.direction) ^ 2))
        * volume (T.carrier ∩ T'.carrier)
      ≤ ENNReal.ofReal
          (Tube.overlapTransversal.C (Module.finrank ℝ E) * (δ : ℝ) ^ (Module.finrank ℝ E)) := by
  have hfin : volume (T.carrier ∩ T'.carrier) ≠ ⊤ :=
    ne_top_of_le_ne_top T.isCompact.measure_lt_top.ne (measure_mono Set.inter_subset_left)
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (Tube.overlapTransversal_toReal hδ hδ1 T T')

/-- (blueprint `def:tubeOverlapCoreClose_constant`) The dimensional dilation factor
`C_{\ref{lem:tubeOverlapCoreClose}} > 1`, depending only on `n`, chosen large enough that the
homothety of a `δ`-tube in `ℝ^n` about its center by this factor captures any `δ`-tube of the same
volume that overlaps it in more than half its volume.

The value `9 + 2·4^n / c_{\ref{le_volume}}(n)` is dictated by the two constraints in the proof of
`Tube.tubeOverlapCoreClose`: the perpendicular drift of the overlapping core is `≤ (2 + K)δ` with
`K = 2·4^n / c_n` the near-parallelism bound coming from `Tube.overlapTransversal`, while the axial
overhang (for `δ ≤ 1`) is absorbed once the dilate half-length exceeds `7/2`. -/
noncomputable def Tube.tubeOverlapCoreClose.C (n : ℕ) : ℝ :=
  9 + 2 * 4 ^ n / (Tube.le_volume.c n : ℝ)

theorem Tube.tubeOverlapCoreClose.one_lt_C (n : ℕ) : 1 < Tube.tubeOverlapCoreClose.C n := by
  have h : (0 : ℝ) ≤ 2 * 4 ^ n / (Tube.le_volume.c n : ℝ) := by positivity
  unfold Tube.tubeOverlapCoreClose.C; linarith

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Distance-to-axis containment for the dilate.** If `w = T.center + s • T.direction` lies on
the core axis of the `δ`-tube `T` with `|s| ≤ C/2`, and a point `z` is within `C·δ` of `w`, then
`z` belongs to the `C`-dilate of `T` (for `C > 0`). This converts a bound on the distance from `z`
to the dilated core axis into membership in the dilate; it is the containment engine behind
`Tube.tubeOverlapCoreClose`. -/
lemma Tube.mem_dilate_of_dist_axis_le {δ : NNReal} (T : Tube δ E) {C : ℝ} (hC : 0 < C)
    {s : ℝ} (hs : |s| ≤ C / 2) {z : E}
    (hz : dist z (T.center + s • T.direction) ≤ C * (δ : ℝ)) :
    z ∈ (Tube.dilate T C).carrier := by
  have hC0 : C ≠ 0 := hC.ne'
  have hCi : (0 : ℝ) < C⁻¹ := inv_pos.mpr hC
  have hcm : T.center = T.midpoint := by
    change midpoint ℝ T.x T.y = (1 / 2 : ℝ) • (T.x + T.y)
    rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
  -- the dilate carrier is the homothety image of the tube's carrier
  rw [Tube.dilate_carrier]
  set w : E := T.center + s • T.direction with hw
  refine ⟨AffineMap.homothety T.center C⁻¹ z, ?_, ?_⟩
  · -- the preimage of `z` lies in `T.carrier`
    have hvw : AffineMap.homothety T.center C⁻¹ w
        = T.center + (C⁻¹ * s) • T.direction := by
      rw [hw, AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_left, smul_smul]
      exact add_comm _ _
    have habs : |C⁻¹ * s| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hCi]
      calc C⁻¹ * |s| ≤ C⁻¹ * (C / 2) := mul_le_mul_of_nonneg_left hs hCi.le
        _ = 1 / 2 := by rw [mul_div_assoc', inv_mul_cancel₀ hC0]
    rw [abs_le] at habs
    have hv_seg : T.center + (C⁻¹ * s) • T.direction ∈ segment ℝ T.x T.y := by
      rw [hcm]
      exact T.midpoint_add_smul_direction_mem_segment (by linarith [habs.1]) habs.2
    have hscale : dist (AffineMap.homothety T.center C⁻¹ z)
        (AffineMap.homothety T.center C⁻¹ w) = C⁻¹ * dist z w := by
      rw [hw]
      simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm]
      rw [add_sub_add_right_eq_sub, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hCi]
    refine T.closedBall_subset_carrier_of_mem_segment hv_seg ?_
    rw [Metric.mem_closedBall, ← hvw, hscale]
    calc C⁻¹ * dist z w ≤ C⁻¹ * (C * (δ : ℝ)) :=
          mul_le_mul_of_nonneg_left hz hCi.le
      _ = (δ : ℝ) := inv_mul_cancel_left₀ hC0 _
  · -- `homothety C ∘ homothety C⁻¹ = id`
    rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ hC0,
      one_smul, sub_add_cancel]

/-- Difference of two affine combinations of the same pair of points. Stated over a bare
`ℝ`-module so that the (costly) `module` normalisation is elaborated in a light context. -/
private lemma affine_comb_sub {M : Type*} [AddCommGroup M] [Module ℝ M] (x y : M) (a b : ℝ) :
    (a • x + (1 - a) • y) - (b • x + (1 - b) • y) = (b - a) • (y - x) := by
  -- (extracted by Fuse golfer)
  rw [add_sub_add_comm, ← sub_smul, ← sub_smul, sub_sub_sub_cancel_left, smul_sub,
    show a - b = -(b - a) from (neg_sub b a).symm, neg_smul, neg_add_eq_sub]

/-- (blueprint `lem:tubeOverlapCoreClose`) Heavy overlap forces containment in the dilate.
If two `δ`-tubes `T, T'` in `ℝ^n` (with `δ ≤ 1`) satisfy `|T ∩ T'| > (1/2)|T|`, then `T'` is
contained in the dilate of `T` about its center by the factor `C_{\ref{lem:tubeOverlapCoreClose}}`.

This is the genuinely `n`-dimensional transversality content of the development: a large overlap
forces the two unit cores to be nearly parallel (via `Tube.overlapTransversal`) and to pass close
to one another, so the whole of `T'` lies in the `C_n`-dilate of `T`. -/
theorem Tube.tubeOverlapCoreClose {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (T T' : Tube δ E)
    (h : (1 / 2 : ENNReal) * volume T.carrier < volume (T.carrier ∩ T'.carrier)) :
    T'.carrier ⊆ (Tube.dilate T (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
  set n := Module.finrank ℝ E with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδr1 : (δ : ℝ) ≤ 1 := NNReal.coe_le_one.mpr hδ1
  set cn : ℝ := (Tube.le_volume.c n : ℝ) with hcn
  have hcn0 : 0 < cn := by rw [hcn]; exact_mod_cast Tube.le_volume.c_pos n
  set u : E := T.direction with hu
  set u' : E := T'.direction with hu'
  have hunorm : ‖u‖ = 1 := T.norm_direction
  have hu'norm : ‖u'‖ = 1 := T'.norm_direction
  set σ : ℝ := Real.sqrt (1 - (inner ℝ u u') ^ 2) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  set K : ℝ := 2 * 4 ^ n / cn with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact div_nonneg (by positivity) hcn0.le
  set Cn : ℝ := Tube.tubeOverlapCoreClose.C n with hCndef
  have hCn_eq : Cn = 9 + K := rfl
  have hCnpos : 0 < Cn := by rw [hCn_eq]; linarith only [hK0]
  set VT : ENNReal := volume T.carrier with hVT
  set A : ENNReal := volume (T.carrier ∩ T'.carrier) with hA
  -- inner products of `u`
  have huu : (inner ℝ u u : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hunorm, one_pow]
  -- squared-norm of the orthogonal projection off `u`
  have key : ∀ w : E, ‖w - (inner ℝ w u) • u‖ ^ 2 = ‖w‖ ^ 2 - (inner ℝ w u) ^ 2 := fun w => by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hunorm, mul_one,
      sq_abs]
    ring
  have hproj_le : ∀ w : E, ‖w - (inner ℝ w u) • u‖ ≤ ‖w‖ := fun w =>
    le_of_sq_le_sq (by rw [key w]; linarith only [sq_nonneg (inner ℝ w u : ℝ)]) (norm_nonneg _)
  have proj_add : ∀ a b : E, (a + b) - (inner ℝ (a + b) u) • u
      = (a - (inner ℝ a u) • u) + (b - (inner ℝ b u) • u) := by
    intro a b; rw [inner_add_left, add_smul]; exact (sub_add_sub_comm _ _ _ _).symm
  have proj_smul_u : ∀ c : ℝ, (c • u) - (inner ℝ (c • u) u) • u = 0 := by
    intro c; rw [real_inner_smul_left, huu, mul_one, sub_self]
  have hproj_u' : ‖u' - (inner ℝ u' u) • u‖ = σ := by
    rw [hσ, show (1 : ℝ) - (inner ℝ u u') ^ 2 = ‖u' - (inner ℝ u' u) • u‖ ^ 2 from by
      rw [key u', hu'norm, real_inner_comm u' u]; ring, Real.sqrt_sq (norm_nonneg _)]
  -- finiteness
  have hVT_fin : VT ≠ ⊤ := T.isCompact.measure_lt_top.ne
  have hA_fin : A ≠ ⊤ := ne_top_of_le_ne_top hVT_fin (measure_mono Set.inter_subset_left)
  have hApos : 0 < A := lt_of_le_of_lt zero_le h
  -- Step A: near-parallelism bound `σ ≤ K δ`.
  have hsin : σ ≤ K * (δ : ℝ) := by
    have htransR : σ * A.toReal ≤ 4 ^ n * (δ : ℝ) ^ n :=
      Tube.overlapTransversal_toReal hδ hδ1 T T'
    have hlvR : cn * (δ : ℝ) ^ (n - 1) ≤ VT.toReal := by
      have hmono := ENNReal.toReal_mono hVT_fin (Tube.le_volume T)
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal, ENNReal.coe_toReal] at hmono
      rwa [hcn]
    have hhalfR : (1 / 2 : ℝ) * VT.toReal ≤ A.toReal := by
      have hmono := ENNReal.toReal_mono hA_fin h.le
      rwa [ENNReal.toReal_mul, one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
        ← one_div] at hmono
    have hlow : (1 / 2 : ℝ) * cn * (δ : ℝ) ^ (n - 1) ≤ A.toReal := by
      linarith only [hlvR, hhalfR]
    have hKδL : (K * (δ : ℝ)) * ((1 / 2 : ℝ) * cn * (δ : ℝ) ^ (n - 1)) = 4 ^ n * (δ : ℝ) ^ n := by
      rw [hK, show (δ : ℝ) ^ n = (δ : ℝ) ^ (n - 1) * (δ : ℝ) from by
          rw [← pow_succ, Nat.sub_add_cancel hnpos],
        div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hcn0.ne']
      ring
    refine le_of_mul_le_mul_right ?_
      (mul_pos (by linarith only [hcn0] : (0:ℝ) < 1 / 2 * cn) (pow_pos hδr (n - 1)))
    rw [hKδL]
    exact le_trans (mul_le_mul_of_nonneg_left hlow hσ0) htransR
  -- A common point of the two tubes.
  obtain ⟨p, hpT, hpT'⟩ := nonempty_of_measure_ne_zero (hA ▸ hApos.ne')
  rw [T.carrier_eq] at hpT
  rw [T'.carrier_eq] at hpT'
  obtain ⟨q1, hq1seg, hq1ball⟩ := Set.mem_iUnion₂.mp hpT
  obtain ⟨q0, hq0seg, hq0ball⟩ := Set.mem_iUnion₂.mp hpT'
  rw [Metric.mem_closedBall] at hq1ball hq0ball
  have hq01 : dist q0 q1 ≤ 2 * (δ : ℝ) :=
    (dist_triangle q0 p q1).trans
      (by rw [dist_comm q0 p]; linarith only [hq0ball, hq1ball])
  -- `q1 - center = (1/2 - a1) • u`.
  have hcm : T.center = (1 / 2 : ℝ) • T.x + (1 - (1 / 2 : ℝ)) • T.y := by
    change midpoint ℝ T.x T.y = _
    rw [midpoint_eq_smul_add, invOf_eq_inv, smul_add]; norm_num
  obtain ⟨a1, b1, ha1, hb1, hab1, hq1eq⟩ := hq1seg
  have hq1c : q1 - T.center = (1 / 2 - a1) • u := by
    rw [hcm, hu, Tube.direction, ← hq1eq, show b1 = 1 - a1 from by linarith only [hab1]]
    exact affine_comb_sub T.x T.y a1 (1 / 2)
  -- Main containment.
  intro z hz
  rw [T'.carrier_eq] at hz
  obtain ⟨z0, hz0seg, hz0ball⟩ := Set.mem_iUnion₂.mp hz
  rw [Metric.mem_closedBall] at hz0ball
  obtain ⟨az, bz, haz, hbz, habz, hz0eq⟩ := hz0seg
  obtain ⟨a0, b0, ha0, hb0, hab0, hq0eq⟩ := hq0seg
  set τ : ℝ := a0 - az with hτ
  have hτ1 : |τ| ≤ 1 := by
    rw [hτ, abs_le]
    exact ⟨by linarith only [ha0, hbz, habz], by linarith only [haz, hb0, hab0]⟩
  have hz0q0 : z0 - q0 = τ • u' := by
    rw [hu', Tube.direction, ← hz0eq, ← hq0eq, hτ,
      show bz = 1 - az from by linarith only [habz], show b0 = 1 - a0 from by linarith only [hab0]]
    exact affine_comb_sub T'.x T'.y az a0
  -- telescoping decomposition
  set d1 : E := z - z0 with hd1
  set d2 : E := z0 - q0 with hd2
  set d3 : E := q0 - q1 with hd3
  set d4 : E := q1 - T.center with hd4
  have hdecomp : z - T.center = d1 + d2 + d3 + d4 := by
    rw [hd1, hd2, hd3, hd4, sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel]
  -- individual perpendicular bounds
  have e1 : ‖d1‖ ≤ (δ : ℝ) := by rwa [hd1, ← dist_eq_norm]
  have e3 : ‖d3‖ ≤ 2 * (δ : ℝ) := by rwa [hd3, ← dist_eq_norm]
  have hb1' : ‖d1 - (inner ℝ d1 u) • u‖ ≤ (δ : ℝ) := (hproj_le d1).trans e1
  have hb3' : ‖d3 - (inner ℝ d3 u) • u‖ ≤ 2 * (δ : ℝ) := (hproj_le d3).trans e3
  have hb2' : ‖d2 - (inner ℝ d2 u) • u‖ ≤ K * (δ : ℝ) := by
    rw [hz0q0, real_inner_smul_left, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, hproj_u']
    linarith only [mul_le_mul_of_nonneg_right hτ1 hσ0, hsin]
  have hb4' : ‖d4 - (inner ℝ d4 u) • u‖ = 0 := by rw [hq1c, proj_smul_u, norm_zero]
  -- perpendicular drift `≤ (K + 3) δ`
  have hprojz : ‖(z - T.center) - (inner ℝ (z - T.center) u) • u‖ ≤ (K + 3) * (δ : ℝ) := by
    rw [hdecomp, proj_add, proj_add, proj_add]
    refine (norm_add₄_le _ _ _ _).trans ?_
    rw [hb4']
    linarith only [hb1', hb2', hb3']
  -- axial parameter `|⟨z - center, u⟩| ≤ 9/2 ≤ Cn/2`
  have hznorm : ‖z - T.center‖ ≤ 9 / 2 := by
    have e2 : ‖d2‖ ≤ 1 := by rwa [hz0q0, norm_smul, Real.norm_eq_abs, hu'norm, mul_one]
    have e4 : ‖d4‖ ≤ 1 / 2 := by
      rw [hq1c, norm_smul, Real.norm_eq_abs, hunorm, mul_one, abs_le]
      exact ⟨by linarith only [hb1, hab1], by linarith only [ha1]⟩
    rw [hdecomp]
    refine (norm_add₄_le _ _ _ _).trans ?_
    linarith only [e1, e2, e3, e4, hδr1]
  have hs_abs : |inner ℝ (z - T.center) u| ≤ Cn / 2 :=
    ((abs_real_inner_le_norm (z - T.center) u).trans_eq (by rw [hunorm, mul_one])).trans
      (by rw [hCn_eq]; linarith only [hznorm, hK0])
  -- conclude via the containment engine
  refine Tube.mem_dilate_of_dist_axis_le T hCnpos hs_abs ?_
  rw [← hu, dist_eq_norm, sub_add_eq_sub_sub]
  exact hprojz.trans (by rw [hCn_eq]; linarith only [hδr.le])

/-- The dimensional volume-ratio constant `C_{\ref{lem:tubeOverlapContainment}}'` of
`Tube.overlapContainment`: the volume of the dilate containing a heavily overlapping tube is at
most this multiple of the original tube's volume. Following the blueprint, which keeps
`C_n' = C_n^{\,n}` abstract, we take it to be exactly the volume-scaling factor
`C_{\ref{lem:tubeOverlapCoreClose}}^{\,n}` of the dilate. -/
noncomputable abbrev Tube.overlapContainment.C (n : ℕ) : ENNReal :=
  ENNReal.ofReal (Tube.tubeDilateVolume.C' n (Tube.tubeOverlapCoreClose.C n))

/-- (blueprint `lem:tubeOverlapContainment`) Heavily overlapping tubes are contained in a dilate.
For a fixed `δ`-tube `T` (with `δ ≤ 1`) there is a convex body `K` of volume at most `C · |T|` that
contains every `δ`-tube `T'` whose intersection with `T` exceeds half of `|T|`.

We take `K` to be the `C_{\ref{lem:tubeOverlapCoreClose}}`-dilate of `T`: containment is
`Tube.tubeOverlapCoreClose`, and the volume identity is `Tube.tubeDilateVolume`. -/
theorem Tube.overlapContainment {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (T : Tube δ E) :
    ∃ K : ConvexSpaceBody E,
      volume K.carrier ≤ Tube.overlapContainment.C (Module.finrank ℝ E) * volume T.carrier ∧
        ∀ (T' : Tube δ E),
          (1 / 2 : ENNReal) * volume T.carrier < volume (T.carrier ∩ T'.carrier) →
            T'.carrier ⊆ K.carrier := by
  refine ⟨Tube.dilate T (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)), ?_,
    fun T' hT' => Tube.tubeOverlapCoreClose hδ hδ1 T T' hT'⟩
  rw [Tube.tubeDilateVolume T (Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E))]

/-- **The dimensional constant in `Kakeya.Tube.volume_dilate_inter_cthickening_ge`.**

It assembles the three ingredients of that estimate: the capsule comparison constant of
`Kakeya.volume_cthickening_le_mul_volume_inter_cthickening`, the tube volume upper bound
constant of `Tube.volume_le`, and (in the denominator) the thickening lower bound constant of
`Tube.le_volume_cthickening`. Only its positivity and the explicit `c ^ n` dilation scaling
matter downstream, never its numerical value. -/
noncomputable def Tube.dilateFullness.C (n : ℕ) : NNReal :=
  (Kakeya.volume_cthickening_le_mul_volume_inter_cthickening.C n : NNReal) *
      _root_.Tube.volume_le.C n / _root_.Tube.le_volume_cthickening.c n

/-- The dimensional constant in `Kakeya.Tube.volume_dilate_inter_cthickening_ge` is positive. -/
theorem Tube.dilateFullness.C_pos (n : ℕ) : 0 < C n := by
  unfold Tube.dilateFullness.C
  exact div_pos
    (mul_pos (by exact_mod_cast Kakeya.volume_cthickening_le_mul_volume_inter_cthickening.C_pos n)
      (_root_.Tube.volume_le.C_pos n))
    (_root_.Tube.le_volume_cthickening.c_pos n)

omit [Nontrivial E] in
/-- **Volume of a tube dilate, for any positive ratio.** This is `Tube.tubeDilateVolume` without
its `1 < C` packaging, which is needed because `Tube.volume_dilate_inter_cthickening_ge` allows the
edge case `c = 1`. -/
private lemma Tube.volume_dilate_eq {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 0 < c) :
    volume (Tube.dilate T c).carrier
      = ENNReal.ofReal (c ^ Module.finrank ℝ E) * volume T.carrier := by
  rw [Tube.dilate_carrier, MeasureTheory.Measure.addHaar_image_homothety,
    abs_of_pos (pow_pos hc (Module.finrank ℝ E))]

omit [Nontrivial E] in
/-- **Capsule trim for a tube dilate.** For `Y` inside the `c`-dilate `K` of a `ρ`-tube with
`c ≥ 1`, the full `2ρ`-neighbourhood of `Y` is comparable to the part of it lying inside `K`.

This is `Kakeya.volume_cthickening_le_mul_volume_inter_cthickening` specialised through
`Tube.dilate_carrier_eq_cthickening`, which exhibits `K` as a capsule of radius `c * ρ`. -/
private lemma Tube.volume_cthickening_le_mul_volume_dilate_inter {ρ : NNReal} (hρ : 0 < ρ)
    {c : ℝ} (hc : 1 ≤ c) (Tρ : Tube ρ E) {Y : Set E} (hY : Y ⊆ (Tube.dilate Tρ c).carrier) :
    volume (Metric.cthickening (2 * (ρ : ℝ)) Y)
      ≤ (Kakeya.volume_cthickening_le_mul_volume_inter_cthickening.C
            (Module.finrank ℝ E) : ENNReal) *
          volume ((Tube.dilate Tρ c).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) Y) := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hρr : (0 : ℝ) < (ρ : ℝ) := NNReal.coe_pos.mpr hρ
  rw [Kakeya.Tube.dilate_carrier_eq_cthickening Tρ hcpos] at hY ⊢
  exact Kakeya.volume_cthickening_le_mul_volume_inter_cthickening isCompact_segment
    (by positivity) (by nlinarith) hY

/-- **The `ENNReal` arithmetic of `Tube.volume_dilate_inter_cthickening_ge`.** Chaining a tube
volume upper bound `hV`, a neighbourhood volume lower bound `hlow` and a capsule trim `htrim`
produces the fullness estimate with the constant `Tube.dilateFullness.C`. Stated abstractly so
that the geometric inputs and the division bookkeeping stay separate. -/
private lemma Tube.dilateFullness_arith (n : ℕ) {cn a r V N I : ENNReal}
    (hV : V ≤ (_root_.Tube.volume_le.C n : ENNReal) * r)
    (hlow : (_root_.Tube.le_volume_cthickening.c n : ENNReal) * a * r ≤ N)
    (htrim : N ≤ (Kakeya.volume_cthickening_le_mul_volume_inter_cthickening.C n : ENNReal) * I) :
    a * (cn * V) ≤ (Tube.dilateFullness.C n : ENNReal) * cn * I := by
  set Ccap : ENNReal := (Kakeya.volume_cthickening_le_mul_volume_inter_cthickening.C n : ENNReal)
  set Cvl : ENNReal := (_root_.Tube.volume_le.C n : ENNReal)
  set clvc : ENNReal := (_root_.Tube.le_volume_cthickening.c n : ENNReal)
  have hclvc0 : clvc ≠ 0 := by
    simp only [clvc]
    exact_mod_cast (_root_.Tube.le_volume_cthickening.c_pos n).ne'
  have hclvctop : clvc ≠ ⊤ := by simp [clvc]
  have hconst : (Tube.dilateFullness.C n : ENNReal) = Ccap * Cvl / clvc := by
    rw [Tube.dilateFullness.C]
    rw [ENNReal.coe_div (_root_.Tube.le_volume_cthickening.c_pos n).ne']
    rw [ENNReal.coe_mul]
    rfl
  have hC : clvc * (a * (cn * V)) ≤ (Ccap * Cvl) * cn * I := by
    calc
      clvc * (a * (cn * V)) ≤ clvc * (a * (cn * (Cvl * r))) := by gcongr
      _ = (clvc * a * r) * (cn * Cvl) := by ring
      _ ≤ N * (cn * Cvl) := by gcongr
      _ ≤ (Ccap * I) * (cn * Cvl) := by gcongr
      _ = (Ccap * Cvl) * cn * I := by ring
  have hdiv : a * (cn * V) ≤ ((Ccap * Cvl) * cn * I) / clvc := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hclvc0) (Or.inl hclvctop)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hC
  have hfinal : ((Ccap * Cvl) * cn * I) / clvc = (Tube.dilateFullness.C n : ENNReal) * cn * I := by
    rw [ENNReal.div_eq_inv_mul]
    rw [hconst]
    rw [ENNReal.div_eq_inv_mul]
    ring
  exact hdiv.trans (le_of_eq hfinal)

/-- **The fullness engine** (GWZ p. 14, l. 562). Let `T` be a `δ`-tube contained in the `c`-dilate
`K` of a `ρ`-tube `Tρ`, with `0 < δ ≤ ρ ≤ 1` and `c ≥ 1`, and let `Y ⊆ T.carrier`. Then the
`2ρ`-neighbourhood of `Y` fills a `c ^ (-n)`-fraction of `K`, degraded only by the density of `Y`
in `T`:

`(|Y| / |T.carrier|) * |K| ≤ C(n) * c ^ n * |K ∩ cthickening (2ρ) Y|`.

Equivalently, `C(n)⁻¹ * c ^ (-n) * (|Y| / |T.carrier|) * |K| ≤ |K ∩ cthickening (2ρ) Y|`; the
form below avoids `ENNReal` inverses. -/
theorem Tube.volume_dilate_inter_cthickening_ge {δ ρ : NNReal} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hρ : ρ ≤ 1) {c : ℝ} (hc : 1 ≤ c) (T : Tube δ E) (Tρ : Tube ρ E)
    (hsub : T.carrier ⊆ (Tube.dilate Tρ c).carrier) {Y : Set E} (hY : Y ⊆ T.carrier) :
    (volume Y / volume T.carrier) * volume (Tube.dilate Tρ c).carrier
      ≤ (Tube.dilateFullness.C (Module.finrank ℝ E) : ENNReal) *
          ENNReal.ofReal (c ^ Module.finrank ℝ E) *
          volume ((Tube.dilate Tρ c).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) Y) := by
  have hρpos : 0 < ρ := hδ.trans_le hδρ
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rw [Tube.volume_dilate_eq Tρ hcpos]
  have hV : volume Tρ.carrier ≤
      (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
        (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
    simpa [ENNReal.coe_mul, ENNReal.coe_pow] using (Tube.volume_le hρ Tρ)
  have hlow :
      (Tube.le_volume_cthickening.c (Module.finrank ℝ E) : ENNReal) *
        (volume Y / volume T.carrier) * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) ≤
        volume (Metric.cthickening (2 * (ρ : ℝ)) Y) :=
    Tube.le_volume_cthickening hδ T ρ hY
  have htrim :
      volume (Metric.cthickening (2 * (ρ : ℝ)) Y) ≤
        (Kakeya.volume_cthickening_le_mul_volume_inter_cthickening.C
            (Module.finrank ℝ E) : ENNReal) *
          volume ((Tube.dilate Tρ c).carrier ∩ Metric.cthickening (2 * (ρ : ℝ)) Y) :=
    Tube.volume_cthickening_le_mul_volume_dilate_inter hρpos hc Tρ (hY.trans hsub)
  exact Tube.dilateFullness_arith (Module.finrank ℝ E) hV hlow htrim

end

end Kakeya
