/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Circular cones

This file defines the open circular cone of height one about a unit vector and records the
geometric and measure-theoretic facts needed for direction packing arguments.
-/

open MeasureTheory ENNReal
open scoped Topology

@[expose] public section

namespace Kakeya.IsBesicovitch.CircularCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The open circular cone of height one and slope `r` about `axis`. The definition is useful
without a unit-length assumption, but its geometric API assumes that `axis` is a unit vector. -/
def cone (axis : E) (r : ℝ) : Set E :=
  {p | inner ℝ p axis ∈ Set.Ioo 0 1 ∧
    ‖p - (inner ℝ p axis : ℝ) • axis‖ < r * inner ℝ p axis}

/-- An open circular cone is a measurable set. -/
lemma measurableSet_cone [MeasurableSpace E] [BorelSpace E] (axis : E) (r : ℝ) :
    MeasurableSet (cone axis r) := by
  have hinner : Continuous (fun p : E => (inner ℝ p axis : ℝ)) :=
    continuous_id.inner continuous_const
  have hperp : Continuous (fun p : E => ‖p - (inner ℝ p axis : ℝ) • axis‖) :=
    (continuous_id.sub (hinner.smul continuous_const)).norm
  exact (measurableSet_Ioo.preimage hinner.measurable).inter
    (measurableSet_lt hperp.measurable (continuous_const.mul hinner).measurable)

/-- A cone point is a positive contraction of a point in the open ball about its axis. The
chosen point in the ball lies in the affine hyperplane normal to the axis. -/
lemma exists_smul_mem_ball {axis p : E} {r : ℝ} (haxis : ‖axis‖ = 1)
    (hp : p ∈ cone axis r) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ b ∈ Metric.ball axis r,
      inner ℝ (b - axis) axis = 0 ∧ p = t • b := by
  let t : ℝ := inner ℝ p axis
  let u : E := p - t • axis
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := hp.1
  have hu : ‖u‖ < r * t := hp.2
  have ht_ne : t ≠ 0 := ne_of_gt ht.1
  let b : E := axis + t⁻¹ • u
  have htu : t • (t⁻¹ • u) = u := by
    rw [← mul_smul, mul_inv_cancel₀ ht_ne, one_smul]
  have hptb : p = t • b := by
    dsimp only [b]
    rw [smul_add, htu]
    dsimp only [u]
    abel
  have hub : ‖t⁻¹ • u‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht.1]
    rw [inv_mul_eq_div]
    rw [div_lt_iff₀ ht.1]
    exact hu
  have hb : b ∈ Metric.ball axis r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [b] using hub
  have hu_orth : inner ℝ u axis = 0 := by
    dsimp only [u, t]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, haxis]
    norm_num
  refine ⟨t, ht, b, hb, ?_, hptb⟩
  dsimp only [b]
  rw [add_sub_cancel_left, real_inner_smul_left, hu_orth, mul_zero]

/-- Radial projection to the unit sphere does not increase the transverse displacement from a
unit axis. -/
lemma dist_inv_norm_smul_add_le_norm {axis u : E} (haxis : ‖axis‖ = 1)
    (hu_orth : inner ℝ u axis = 0) :
    dist (‖axis + u‖⁻¹ • (axis + u)) axis ≤ ‖u‖ := by
  let q : E := axis + u
  let s : ℝ := ‖q‖
  have hq_ne : q ≠ 0 := by
    intro hq
    have hinner : inner ℝ q axis = 1 := by
      dsimp only [q]
      rw [inner_add_left, hu_orth, add_zero, real_inner_self_eq_norm_sq, haxis]
      norm_num
    rw [hq, inner_zero_left] at hinner
    norm_num at hinner
  have hs_pos : 0 < s := by simpa [s] using norm_pos_iff.mpr hq_ne
  have hs_sq : s ^ 2 = 1 + ‖u‖ ^ 2 := by
    change ‖axis + u‖ ^ 2 = 1 + ‖u‖ ^ 2
    rw [pow_two, norm_add_sq_eq_norm_sq_add_norm_sq_real]
    · rw [haxis]
      ring
    · rw [real_inner_comm]
      exact hu_orth
  have hs_one : 1 ≤ s := by
    nlinarith [sq_nonneg ‖u‖, sq_nonneg (s - 1), hs_pos]
  have hs_inv : s * s⁻¹ = 1 := mul_inv_cancel₀ hs_pos.ne'
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs_pos.le
  have hs_inv_le : s⁻¹ ≤ 1 := (inv_le_one₀ hs_pos).2 hs_one
  have hnormq : ‖s⁻¹ • q‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs_inv_nonneg]
    change s⁻¹ * s = 1
    exact inv_mul_cancel₀ hs_pos.ne'
  have hinnerq : inner ℝ (s⁻¹ • q) axis = s⁻¹ := by
    rw [real_inner_smul_left]
    have : inner ℝ q axis = 1 := by
      dsimp only [q]
      rw [inner_add_left, hu_orth, add_zero, real_inner_self_eq_norm_sq, haxis]
      norm_num
    rw [this, mul_one]
  have hdist_sq : dist (s⁻¹ • q) axis ^ 2 = 2 - 2 * s⁻¹ := by
    rw [dist_eq_norm, norm_sub_sq_real, hnormq, haxis, hinnerq]
    ring
  have hsecond : 0 ≤ s + 1 - 2 * s⁻¹ := by linarith
  have hfactor : 0 ≤ (s - 1) * (s + 1 - 2 * s⁻¹) :=
    mul_nonneg (sub_nonneg.mpr hs_one) hsecond
  have hsq_le : dist (s⁻¹ • q) axis ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [hdist_sq]
    nlinarith
  have hdist_nonneg : 0 ≤ dist (s⁻¹ • q) axis := dist_nonneg
  have hu_nonneg : 0 ≤ ‖u‖ := norm_nonneg _
  change dist (s⁻¹ • q) axis ≤ ‖u‖
  nlinarith

/-- Every ray in a cone points within distance `r` of the cone axis after normalization. -/
lemma dist_inv_norm_smul_lt {axis p : E} {r : ℝ} (haxis : ‖axis‖ = 1)
    (hp : p ∈ cone axis r) : dist (‖p‖⁻¹ • p) axis < r := by
  let t : ℝ := inner ℝ p axis
  let u : E := p - t • axis
  have ht : 0 < t := hp.1.1
  have hu : ‖u‖ < r * t := hp.2
  have ht_ne : t ≠ 0 := ht.ne'
  have hp_eq : p = t • (axis + t⁻¹ • u) := by
    rw [smul_add, ← mul_smul, mul_inv_cancel₀ ht_ne, one_smul]
    dsimp only [u]
    abel
  have hu_scaled : ‖t⁻¹ • u‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_eq_div,
      div_lt_iff₀ ht]
    exact hu
  have hu_orth : inner ℝ (t⁻¹ • u) axis = 0 := by
    rw [real_inner_smul_left]
    have : inner ℝ u axis = 0 := by
      dsimp only [u, t]
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, haxis]
      norm_num
    rw [this, mul_zero]
  have hq_ne : axis + t⁻¹ • u ≠ 0 := by
    intro hq
    have hinner : inner ℝ (axis + t⁻¹ • u) axis = 1 := by
      rw [inner_add_left, hu_orth, add_zero, real_inner_self_eq_norm_sq, haxis]
      norm_num
    rw [hq, inner_zero_left] at hinner
    norm_num at hinner
  rw [hp_eq, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_inv, smul_smul]
  have hcoef : t⁻¹ * ‖axis + t⁻¹ • u‖⁻¹ * t = ‖axis + t⁻¹ • u‖⁻¹ := by
    calc
      _ = (t⁻¹ * t) * ‖axis + t⁻¹ • u‖⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ ht_ne, one_mul]
  rw [hcoef]
  exact (dist_inv_norm_smul_add_le_norm haxis hu_orth).trans_lt hu_scaled

/-- Cones of slope `r` about unit axes at distance at least `δ` are disjoint when
`2 * r ≤ δ`. -/
lemma disjoint_cone {axis₁ axis₂ : E} {r δ : ℝ} (haxis₁ : ‖axis₁‖ = 1)
    (haxis₂ : ‖axis₂‖ = 1) (hsep : δ ≤ dist axis₁ axis₂) (hr : 2 * r ≤ δ) :
    Disjoint (cone axis₁ r) (cone axis₂ r) := by
  rw [Set.disjoint_left]
  intro p hp₁ hp₂
  let n : E := ‖p‖⁻¹ • p
  have h₁ : dist n axis₁ < r := dist_inv_norm_smul_lt haxis₁ hp₁
  have h₂ : dist n axis₂ < r := dist_inv_norm_smul_lt haxis₂ hp₂
  have hdist : dist axis₁ axis₂ < 2 * r := by
    calc
      dist axis₁ axis₂ ≤ dist axis₁ n + dist n axis₂ := dist_triangle _ _ _
      _ < r + r := add_lt_add (by simpa [dist_comm] using h₁) h₂
      _ = 2 * r := by ring
  linarith

/-- A cone lies in any convex set that contains the origin and the corresponding open ball around
its unit axis. -/
lemma cone_subset_convex {axis : E} {r : ℝ} {D : Set E} (haxis : ‖axis‖ = 1)
    (hD : Convex ℝ D) (hzero : (0 : E) ∈ D) (hball : Metric.ball axis r ⊆ D) :
    cone axis r ⊆ D := by
  intro p hp
  obtain ⟨t, ht, b, hb, -, rfl⟩ := exists_smul_mem_ball haxis hp
  exact hD.smul_mem_of_zero_mem hzero (hball hb) ⟨ht.1.le, ht.2.le⟩

section Volume

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- In dimension three, the volume of the height-one circular cone of slope `r` is
`π * r ^ 2 / 3`. -/
lemma volume_cone {axis : E} {r : ℝ} (hfin : Module.finrank ℝ E = 3)
    (haxis : ‖axis‖ = 1) (hr : 0 ≤ r) :
    volume (cone axis r) = ENNReal.ofReal (Real.pi * r ^ 2 / 3) := by
  set K : Submodule ℝ E := ℝ ∙ axis with hK_def
  let φ : ℝ ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.toSpanUnitSingleton axis haxis
  let e₁ : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E)) :=
    K.orthogonalDecomposition.trans
      (LinearIsometryEquiv.withLpProdCongr 2 φ.symm
        (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E)))
  let f : E → ℝ × (Kᗮ : Submodule ℝ E) := fun p => WithLp.ofLp (e₁ p)
  let R : Set (ℝ × (Kᗮ : Submodule ℝ E)) :=
    {q | q.1 ∈ Set.Ioo 0 1 ∧ ‖q.2‖ < r * q.1}
  have hf_mp : MeasurePreserving f := by
    have h₁ : MeasurePreserving (e₁ : E → WithLp 2 (ℝ × (Kᗮ : Submodule ℝ E))) :=
      e₁.measurePreserving
    have h₂ : MeasurePreserving (@WithLp.ofLp 2 (ℝ × (Kᗮ : Submodule ℝ E))) :=
      WithLp.volume_preserving_ofLp ℝ (Kᗮ : Submodule ℝ E)
    exact h₂.comp h₁
  have h_eq : cone axis r = f ⁻¹' R := by
    ext p
    simp only [cone, Set.mem_setOf_eq, Set.mem_preimage, R]
    have hfp_e₁ : e₁ p =
        WithLp.toLp 2 (φ.symm (K.orthogonalProjectionOnto p),
          (Kᗮ.orthogonalProjectionOnto p : Kᗮ)) := by
      change LinearIsometryEquiv.withLpProdCongr 2 φ.symm
              (LinearIsometryEquiv.refl ℝ (Kᗮ : Submodule ℝ E))
              (K.orthogonalDecomposition p) = _
      rw [Submodule.orthogonalDecomposition_apply]
      simp [LinearIsometryEquiv.withLpProdCongr]
    have hK_proj : K.orthogonalProjectionOnto p = φ (inner ℝ p axis) := by
      apply Subtype.ext
      change K.starProjection p = (inner ℝ p axis : ℝ) • axis
      rw [Submodule.starProjection_unit_singleton (𝕜 := ℝ) haxis, real_inner_comm]
    have hfp_fst : (f p).1 = inner ℝ p axis := by
      change (e₁ p).ofLp.1 = inner ℝ p axis
      rw [hfp_e₁]
      change φ.symm (K.orthogonalProjectionOnto p) = inner ℝ p axis
      rw [hK_proj, LinearIsometryEquiv.symm_apply_apply]
    have hfp_snd_norm : ‖(f p).2‖ = ‖p - (inner ℝ p axis : ℝ) • axis‖ := by
      change ‖(e₁ p).ofLp.2‖ = _
      rw [hfp_e₁]
      change ‖(Kᗮ.orthogonalProjectionOnto p : Kᗮ)‖ = _
      rw [show ‖(Kᗮ.orthogonalProjectionOnto p : Kᗮ)‖ =
            ‖((Kᗮ.orthogonalProjectionOnto p : Kᗮ) : E)‖ from rfl,
        Submodule.coe_orthogonalProjectionOnto_apply,
        Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_unit_singleton (𝕜 := ℝ) haxis,
        real_inner_comm]
    rw [hfp_fst, hfp_snd_norm]
  have hR_meas : MeasurableSet R := by
    exact (measurableSet_Ioo.preimage measurable_fst).inter
      (measurableSet_lt measurable_snd.norm (measurable_const.mul measurable_fst))
  have haxis_ne : axis ≠ 0 := by
    intro h
    rw [h, norm_zero] at haxis
    norm_num at haxis
  have hK_finrank : Module.finrank ℝ (Kᗮ : Submodule ℝ E) = 2 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [hK_def, finrank_span_singleton haxis_ne, hfin]
  have hball (t : ℝ) :
      volume (Metric.ball (0 : (Kᗮ : Submodule ℝ E)) (r * t)) =
        ENNReal.ofReal (r * t) ^ 2 * ENNReal.ofReal Real.pi := by
    haveI : Nontrivial (Kᗮ : Submodule ℝ E) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hK_finrank]; omega)
    simpa [hK_finrank] using
      (InnerProductSpace.volume_ball_of_dim_even (E := (Kᗮ : Submodule ℝ E))
        (k := 1) (by omega) (0 : Kᗮ) (r * t))
  have hfiber (t : ℝ) : Prod.mk t ⁻¹' R =
      if t ∈ Set.Ioo (0 : ℝ) 1 then Metric.ball (0 : (Kᗮ : Submodule ℝ E)) (r * t)
      else ∅ := by
    ext u
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
    · rw [if_pos ht]
      change (t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖u‖ < r * t) ↔
        u ∈ Metric.ball (0 : (Kᗮ : Submodule ℝ E)) (r * t)
      simp only [Metric.mem_ball, dist_zero_right, ht, true_and]
    · rw [if_neg ht]
      change (t ∈ Set.Ioo (0 : ℝ) 1 ∧ ‖u‖ < r * t) ↔ False
      simp [ht]
  rw [h_eq, hf_mp.measure_preimage hR_meas.nullMeasurableSet,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_apply hR_meas]
  simp_rw [hfiber]
  have hindicator :
      (fun t : ℝ => volume (if t ∈ Set.Ioo (0 : ℝ) 1 then
        Metric.ball (0 : (Kᗮ : Submodule ℝ E)) (r * t) else ∅)) =
      (Set.Ioo (0 : ℝ) 1).indicator
        (fun t => volume (Metric.ball (0 : (Kᗮ : Submodule ℝ E)) (r * t))) := by
    funext t
    by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1 <;> simp [ht]
  rw [hindicator]
  rw [lintegral_indicator measurableSet_Ioo]
  simp_rw [hball]
  have hpointwise : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (r * t) ^ 2 * ENNReal.ofReal Real.pi =
        ENNReal.ofReal (Real.pi * r ^ 2 * t ^ 2) := by
    intro t ht
    rw [← ENNReal.ofReal_pow (mul_nonneg hr ht.1.le),
      ← ENNReal.ofReal_mul (sq_nonneg (r * t))]
    congr 1
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioo hpointwise]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [integral_pow]
    norm_num
    ring
  · change IntegrableOn (fun x : ℝ => Real.pi * r ^ 2 * x ^ 2) (Set.Ioc 0 1)
    rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (continuous_const.mul (continuous_id.pow 2)).continuousOn.integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    positivity

/-- Real-valued form of `volume_cone`. -/
lemma volume_real_cone {axis : E} {r : ℝ} (hfin : Module.finrank ℝ E = 3)
    (haxis : ‖axis‖ = 1) (hr : 0 ≤ r) :
    volume.real (cone axis r) = Real.pi * r ^ 2 / 3 := by
  rw [measureReal_def, volume_cone hfin haxis hr, ENNReal.toReal_ofReal]
  positivity

/-- The cone of slope `δ / 2` has volume `π * δ ^ 2 / 12`. -/
lemma volume_real_cone_half {axis : E} {δ : ℝ} (hfin : Module.finrank ℝ E = 3)
    (haxis : ‖axis‖ = 1) (hδ : 0 ≤ δ) :
    volume.real (cone axis (δ / 2)) = Real.pi * δ ^ 2 / 12 := by
  rw [volume_real_cone hfin haxis (div_nonneg hδ zero_le_two)]
  ring

end Volume

end Kakeya.IsBesicovitch.CircularCone
