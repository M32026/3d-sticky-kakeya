import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import MyLeanRepo.Kakeya.Assouad.IntersectionDiameterBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseDirectionPacking.GeometricOverlap
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Geometry helpers for WZ1 Lemma 17 cube count

Extracted from `WZ1LocalGrainCubeCount.lean`:
1. `volume_by_three_diameters_public` — volume bound via coordinate diameters
2. `tube_intersection_volume_cross_bound` — intersection volume via cross norm
3. `covering_number_from_slab_volumes` — covering number from slab estimates
4. `transverse_fine_exists` — transverse fine tube from close-direction count
-/

namespace Kakeya.Assouad

open Kakeya MeasureTheory Metric

lemma volume_by_three_diameters_public {E : Set Point3} (hE : MeasurableSet E)
    (A : Point3 ≃ₗᵢ[ℝ] Point3)
    (d0 d1 d2 : ℝ) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (h0 : ∀ x y, x ∈ E → y ∈ E → |(A x) 0 - (A y) 0| ≤ d0)
    (h1 : ∀ x y, x ∈ E → y ∈ E → |(A x) 1 - (A y) 1| ≤ d1)
    (h2 : ∀ x y, x ∈ E → y ∈ E → |(A x) 2 - (A y) 2| ≤ d2) :
    volume E ≤ ENNReal.ofReal (d0 * d1 * d2) := by
  let F : Point3 → (Fin 3 → ℝ) := WithLp.ofLp (p := 2)
  let Finv : (Fin 3 → ℝ) → Point3 := WithLp.toLp (p := 2)
  let F_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := F
      invFun := Finv
      left_inv := WithLp.toLp_ofLp (p := 2)
      right_inv := WithLp.ofLp_toLp (p := 2)
      measurable_toFun := (PiLp.volume_preserving_ofLp (ι := Fin 3)).measurable
      measurable_invFun := (PiLp.continuous_toLp 2 (β := fun (_ : Fin 3) => ℝ)).measurable }
  let G_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) := A.toMeasurableEquiv.trans F_equiv
  let G : Point3 → (Fin 3 → ℝ) := G_equiv
  let AE : Set (Fin 3 → ℝ) := G '' E
  have hpresG : MeasurePreserving G volume volume :=
    (PiLp.volume_preserving_ofLp (ι := Fin 3)).comp A.measurePreserving
  have hAE_meas : MeasurableSet AE := G_equiv.measurableSet_image.mpr hE
  have hvol : volume E = volume AE := by
    have hmap : Measure.map G volume = volume := hpresG.map_eq
    have hG_inj : Function.Injective G := G_equiv.injective
    have hpre : G ⁻¹' AE = E := Set.preimage_image_eq _ hG_inj
    have h1 : volume (G ⁻¹' AE) = Measure.map G volume AE :=
      (Measure.map_apply hpresG.measurable hAE_meas).symm
    rw [hpre] at h1
    exact h1.trans (by rw [hmap])
  have hmain : volume AE ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' AE) :=
    Real.volume_pi_le_prod_diam AE
  have h_ediam : ∀ i : Fin 3, Metric.ediam (Function.eval i '' AE) ≤ ENNReal.ofReal
      (match i with | 0 => d0 | 1 => d1 | 2 => d2) := by
    intro i
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rcases ha with ⟨g, hg, ha_eq⟩
    rcases hg with ⟨x, hx, hg_eq⟩
    rcases hb with ⟨g', hg', hb_eq⟩
    rcases hg' with ⟨y, hy, hg'_eq⟩
    have h_goal : dist a b = |(A x) i - (A y) i| := by
      rw [←ha_eq, ←hb_eq, ←hg_eq, ←hg'_eq]
      simp [G, F, Real.dist_eq] <;> rfl
    rw [h_goal]
    fin_cases i <;> [exact h0 x y hx hy; exact h1 x y hx hy; exact h2 x y hx hy]
  have hprod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' AE)) ≤
      ENNReal.ofReal (d0 * d1 * d2) := by
    have h_expand : (∏ i : Fin 3, Metric.ediam (Function.eval i '' AE)) =
        Metric.ediam (Function.eval 0 '' AE) * Metric.ediam (Function.eval 1 '' AE) *
        Metric.ediam (Function.eval 2 '' AE) := by
      simp [Fin.prod_univ_succ] <;> ring
    rw [h_expand]
    have hmul : ENNReal.ofReal d0 * ENNReal.ofReal d1 * ENNReal.ofReal d2 =
        ENNReal.ofReal (d0 * d1 * d2) := by
      rw [← ENNReal.ofReal_mul hd0, ← ENNReal.ofReal_mul (mul_nonneg hd0 hd1)] <;> ring
    rw [← hmul]
    have h0' : Metric.ediam (Function.eval 0 '' AE) ≤ ENNReal.ofReal d0 := h_ediam 0
    have h1' : Metric.ediam (Function.eval 1 '' AE) ≤ ENNReal.ofReal d1 := h_ediam 1
    have h2' : Metric.ediam (Function.eval 2 '' AE) ≤ ENNReal.ofReal d2 := h_ediam 2
    gcongr
  calc volume E = volume AE := hvol
    _ ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' AE) := hmain
    _ ≤ ENNReal.ofReal (d0 * d1 * d2) := hprod
/-- Internal helper: three-diameter bound once v, θ are fixed. -/
private lemma main_cross_proof {δ : ℝ} (hδ : 0 < δ)
    (T U : DeltaTube δ) (v : Point3)
    (h_v_choice : v = U.direction ∨ v = -U.direction)
    (θ : ℝ) (hθ_nonneg : 0 ≤ θ) (hθ_le : θ ≤ Real.pi / 2)
    (hcos : inner ℝ T.direction v = Real.cos θ)
    (hsin_pos : 0 < Real.sin θ)
    (hsin_eq : Real.sin θ = ‖wz1Cross T.direction U.direction‖) :
    volume (T.carrier ∩ U.carrier) ≤
      ENNReal.ofReal (16 * δ^3 / ‖wz1Cross T.direction U.direction‖) := by
  let S : Set Point3 := T.carrier ∩ U.carrier
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1_std : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2_std : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have hv_norm : ‖v‖ = 1 := by
    cases h_v_choice with
    | inl h => rw [h]; exact U.direction_unit
    | inr h => rw [h]; rw [norm_neg]; exact U.direction_unit
  have he0_std_norm : ‖e0_std‖ = 1 := by simp [e0_std]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (v - e0_std))ᗮ
  have hA : A v = e0_std :=
    Submodule.reflection_sub (by rw [hv_norm, he0_std_norm])
  let e2 : Point3 := A.symm e1_std
  let e3 : Point3 := A.symm e2_std
  have hA_e2 : A e2 = e1_std := by simp [e2]
  have hA_e3 : A e3 = e2_std := by simp [e3]
  have he2_norm : ‖e2‖ = 1 := by
    have h : ‖e2‖ = ‖e1_std‖ := A.symm.norm_map e1_std
    rw [h] <;> simp [e1_std]
  have he3_norm : ‖e3‖ = 1 := by
    have h : ‖e3‖ = ‖e2_std‖ := A.symm.norm_map e2_std
    rw [h] <;> simp [e2_std]
  have he2_orth_v : inner ℝ e2 v = 0 := by
    have h : inner ℝ e2 v = inner ℝ (A e2) (A v) := (A.inner_map_map e2 v).symm
    rw [h, hA_e2, hA]
    have h_zero : inner ℝ e1_std e0_std = 0 := by
      have h := EuclideanSpace.inner_single_right 0 (1 : ℝ) e1_std
      simpa [e0_std, e1_std, EuclideanSpace.single_apply] using h
    exact h_zero
  have he3_orth_v : inner ℝ e3 v = 0 := by
    have h : inner ℝ e3 v = inner ℝ (A e3) (A v) := (A.inner_map_map e3 v).symm
    rw [h, hA_e3, hA]
    have h_zero : inner ℝ e2_std e0_std = 0 := by
      have h := EuclideanSpace.inner_single_right 0 (1 : ℝ) e2_std
      simpa [e0_std, e2_std, EuclideanSpace.single_apply] using h
    exact h_zero
  have he2_orth_U : inner ℝ U.direction e2 = 0 := by
    have h_comm : inner ℝ U.direction e2 = inner ℝ e2 U.direction :=
      (real_inner_comm U.direction e2).symm
    rw [h_comm]
    cases h_v_choice with
    | inl h =>
      have hU : U.direction = v := h.symm
      rw [hU]; exact he2_orth_v
    | inr h =>
      have hU : U.direction = -v := neg_eq_iff_eq_neg.mp h.symm
      rw [hU, inner_neg_right, he2_orth_v] <;> ring
  have he3_orth_U : inner ℝ U.direction e3 = 0 := by
    have h_comm : inner ℝ U.direction e3 = inner ℝ e3 U.direction :=
      (real_inner_comm U.direction e3).symm
    rw [h_comm]
    cases h_v_choice with
    | inl h =>
      have hU : U.direction = v := h.symm
      rw [hU]; exact he3_orth_v
    | inr h =>
      have hU : U.direction = -v := neg_eq_iff_eq_neg.mp h.symm
      rw [hU, inner_neg_right, he3_orth_v] <;> ring
  have hcoord0 : ∀ (z : Point3), (A z) 0 = inner ℝ z v := by
    intro z
    have h : (A z) 0 = inner ℝ (A z) e0_std := by
      have h2 : inner ℝ (A z) e0_std = (1 : ℝ) * (A z) 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e0_std = inner ℝ z (A.symm e0_std) := by
      have h4 := A.inner_map_map z (A.symm e0_std)
      have h5 : A (A.symm e0_std) = e0_std := A.apply_symm_apply e0_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e0_std = v := by
      have h7 : A (A.symm e0_std) = A v := by rw [A.apply_symm_apply, hA]
      exact A.injective h7
    rw [h6]
  have hcoord1 : ∀ (z : Point3), (A z) 1 = inner ℝ z e2 := by
    intro z
    have h : (A z) 1 = inner ℝ (A z) e1_std := by
      have h2 : inner ℝ (A z) e1_std = (1 : ℝ) * (A z) 1 :=
        EuclideanSpace.inner_single_right 1 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e1_std = inner ℝ z (A.symm e1_std) := by
      have h4 := A.inner_map_map z (A.symm e1_std)
      have h5 : A (A.symm e1_std) = e1_std := A.apply_symm_apply e1_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl
  have hcoord2 : ∀ (z : Point3), (A z) 2 = inner ℝ z e3 := by
    intro z
    have h : (A z) 2 = inner ℝ (A z) e2_std := by
      have h2 : inner ℝ (A z) e2_std = (1 : ℝ) * (A z) 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e2_std = inner ℝ z (A.symm e2_std) := by
      have h4 := A.inner_map_map z (A.symm e2_std)
      have h5 : A (A.symm e2_std) = e2_std := A.apply_symm_apply e2_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl
  let d0 : ℝ := 2 * δ * (1 + Real.cos θ) / Real.sin θ
  let d1 : ℝ := 2 * δ
  let d2 : ℝ := 2 * δ
  have hθ_lower : -(Real.pi / 2) ≤ θ := by
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have h : -(Real.pi / 2) ≤ 0 := by linarith
    linarith [hθ_nonneg]
  have hcos_nonneg : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨hθ_lower, hθ_le⟩
  have hd0_nonneg : 0 ≤ d0 := by
    dsimp only [d0]
    apply div_nonneg
    · have h' : 0 ≤ 1 + Real.cos θ := by linarith [Real.neg_one_le_cos θ]
      positivity
    · exact hsin_pos.le
  have hd1_nonneg : 0 ≤ d1 := by positivity
  have hd2_nonneg : 0 ≤ d2 := by positivity
  have h0 : ∀ x y, x ∈ S → y ∈ S → |(A x) 0 - (A y) 0| ≤ d0 := by
    intro x y hx hy
    rw [hcoord0 x, hcoord0 y]
    have h : inner ℝ x v - inner ℝ y v = inner ℝ (x - y) v := by rw [inner_sub_left]
    rw [h]
    exact intersection_axial_diameter_bound (by linarith) T U v h_v_choice θ
      hθ_nonneg hθ_le hcos hsin_pos x y hx hy
  have h1 : ∀ x y, x ∈ S → y ∈ S → |(A x) 1 - (A y) 1| ≤ d1 := by
    intro x y hx hy
    rw [hcoord1 x, hcoord1 y]
    have hbx : |inner ℝ x e2 - inner ℝ U.base e2| ≤ δ :=
      transverse_projection_bound (by linarith) T U e2 he2_norm he2_orth_U x hx
    have hby : |inner ℝ y e2 - inner ℝ U.base e2| ≤ δ :=
      transverse_projection_bound (by linarith) T U e2 he2_norm he2_orth_U y hy
    have h : |inner ℝ x e2 - inner ℝ y e2| ≤
        |inner ℝ x e2 - inner ℝ U.base e2| + |inner ℝ y e2 - inner ℝ U.base e2| := by
      have h_eq : inner ℝ x e2 - inner ℝ y e2 =
          (inner ℝ x e2 - inner ℝ U.base e2) - (inner ℝ y e2 - inner ℝ U.base e2) := by ring
      rw [h_eq]; exact abs_sub _ _
    linarith
  have h2 : ∀ x y, x ∈ S → y ∈ S → |(A x) 2 - (A y) 2| ≤ d2 := by
    intro x y hx hy
    rw [hcoord2 x, hcoord2 y]
    have hbx : |inner ℝ x e3 - inner ℝ U.base e3| ≤ δ :=
      transverse_projection_bound (by linarith) T U e3 he3_norm he3_orth_U x hx
    have hby : |inner ℝ y e3 - inner ℝ U.base e3| ≤ δ :=
      transverse_projection_bound (by linarith) T U e3 he3_norm he3_orth_U y hy
    have h : |inner ℝ x e3 - inner ℝ y e3| ≤
        |inner ℝ x e3 - inner ℝ U.base e3| + |inner ℝ y e3 - inner ℝ U.base e3| := by
      have h_eq : inner ℝ x e3 - inner ℝ y e3 =
          (inner ℝ x e3 - inner ℝ U.base e3) - (inner ℝ y e3 - inner ℝ U.base e3) := by ring
      rw [h_eq]; exact abs_sub _ _
    linarith
  have hS_meas : MeasurableSet S :=
    (Metric.isClosed_cthickening).measurableSet.inter (Metric.isClosed_cthickening).measurableSet
  have hvol_bound : volume S ≤ ENNReal.ofReal (d0 * d1 * d2) :=
    volume_by_three_diameters_public hS_meas A d0 d1 d2 hd0_nonneg hd1_nonneg hd2_nonneg h0 h1 h2
  have h_expr : d0 * d1 * d2 = 8 * δ ^ 3 * (1 + Real.cos θ) / Real.sin θ := by
    dsimp only [d0, d1, d2] <;> ring
  have hcos_le_one : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h_final : d0 * d1 * d2 ≤ 16 * δ ^ 3 / Real.sin θ := by
    rw [h_expr]
    have h : 1 + Real.cos θ ≤ 2 := by linarith
    have hpos : 0 < Real.sin θ := hsin_pos
    have h4 : 8 * δ ^ 3 * (1 + Real.cos θ) ≤ 16 * δ ^ 3 := by
      calc 8 * δ ^ 3 * (1 + Real.cos θ) ≤ 8 * δ ^ 3 * 2 := by gcongr
        _ = 16 * δ ^ 3 := by ring
    have hstep : 8 * δ ^ 3 * (1 + Real.cos θ) / Real.sin θ ≤ 16 * δ ^ 3 / Real.sin θ :=
      div_le_div_of_nonneg_right h4 hpos.le
    exact hstep
  have h_sin_eq_cross : Real.sin θ = ‖wz1Cross T.direction U.direction‖ := hsin_eq
  rw [h_sin_eq_cross] at h_final
  exact hvol_bound.trans (ENNReal.ofReal_le_ofReal h_final)
/-- Quantitative intersection volume bound for two misaligned δ-tubes.

If `‖cross(T.direction, U.direction)‖ ≥ 32δ`, then
`volume(T.carrier ∩ U.carrier) ≤ 16δ³ / ‖cross‖`.

This is the sharper three-diameter bound underlying
`misaligned_tubes_intersection_volume_upper`, expressed directly in terms
of the cross-product norm.  Intersecting with any ball only reduces the
volume, so the same bound holds for `T.carrier ∩ U.carrier ∩ B`. -/
lemma tube_intersection_volume_cross_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000)
    (T U : DeltaTube δ)
    (hcross : 32 * δ ≤ ‖wz1Cross T.direction U.direction‖) :
    volume (T.carrier ∩ U.carrier) ≤
      ENNReal.ofReal (16 * δ^3 / ‖wz1Cross T.direction U.direction‖) := by
  have hcross_pos : 0 < ‖wz1Cross T.direction U.direction‖ := by
    have h : 0 < 32 * δ := by positivity
    exact h.trans_le hcross
  have h1_main : ‖wz1Cross T.direction U.direction‖ ^ 2 =
      1 - (inner ℝ T.direction U.direction)^2 :=
    cross_norm_sq T.direction U.direction T.direction_unit U.direction_unit
  have hinner_lt_one : inner ℝ T.direction U.direction < 1 := by
    nlinarith [norm_nonneg (wz1Cross T.direction U.direction)]
  have hinner_gt_neg_one : -1 < inner ℝ T.direction U.direction := by
    nlinarith [norm_nonneg (wz1Cross T.direction U.direction)]
  -- Choose v = U.direction or -U.direction so inner(T.dir, v) ≥ 0
  by_cases hpos : 0 < inner ℝ T.direction U.direction
  · let v : Point3 := U.direction
    let θ : ℝ := Real.arccos (inner ℝ T.direction v)
    have hθ_pos : 0 < θ := by
      have h : inner ℝ T.direction v < 1 := by
        exact_mod_cast hinner_lt_one
      exact Real.arccos_pos.mpr h
    have hθ_le : θ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr (by linarith)
    have h31 : -1 ≤ inner ℝ T.direction v := by linarith [hinner_gt_neg_one]
    have h32 : inner ℝ T.direction v ≤ 1 := by linarith [hinner_lt_one]
    have hcos : inner ℝ T.direction v = Real.cos θ := (Real.cos_arccos h31 h32).symm
    have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos (by linarith [Real.pi_pos])
    have hsin_eq : Real.sin θ = ‖wz1Cross T.direction U.direction‖ := by
      have h2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq_add_cos_sq θ ▸ by ring
      have hcos2 : (inner ℝ T.direction U.direction)^2 = (Real.cos θ)^2 := by
        have h_eq : inner ℝ T.direction U.direction = inner ℝ T.direction v := by rfl
        rw [h_eq, hcos]
      have h3 : Real.sin θ ^ 2 = ‖wz1Cross T.direction U.direction‖ ^ 2 := by linarith
      nlinarith [hsin_pos, norm_nonneg (wz1Cross T.direction U.direction)]
    exact main_cross_proof hδ T U v (Or.inl rfl) θ hθ_pos.le hθ_le hcos hsin_pos hsin_eq
  · have hneg : inner ℝ T.direction U.direction ≤ 0 := by linarith
    let v : Point3 := -U.direction
    have hinner_v : inner ℝ T.direction v = -inner ℝ T.direction U.direction := by
      simp [v, inner_neg_right] <;> ring
    have hpos2 : 0 ≤ inner ℝ T.direction v := by
      linarith [hinner_v]
    have hinner_v_lt_one : inner ℝ T.direction v < 1 := by
      linarith [hinner_v, hinner_gt_neg_one]
    let θ : ℝ := Real.arccos (inner ℝ T.direction v)
    have hθ_pos : 0 < θ := Real.arccos_pos.mpr hinner_v_lt_one
    have hθ_le : θ ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr hpos2
    have h31 : -1 ≤ inner ℝ T.direction v := by linarith
    have h32 : inner ℝ T.direction v ≤ 1 := by linarith
    have hcos : inner ℝ T.direction v = Real.cos θ := (Real.cos_arccos h31 h32).symm
    have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos (by linarith [Real.pi_pos])
    have hsin_eq : Real.sin θ = ‖wz1Cross T.direction U.direction‖ := by
      have h2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq_add_cos_sq θ ▸ by ring
      have hcos2 : (inner ℝ T.direction v)^2 = (Real.cos θ)^2 := by rw [hcos]
      have hinner_sq : (inner ℝ T.direction U.direction)^2 = (inner ℝ T.direction v)^2 := by
        rw [hinner_v] <;> ring
      have h3 : Real.sin θ ^ 2 = ‖wz1Cross T.direction U.direction‖ ^ 2 := by
        linarith [h1_main, h2, hcos2, hinner_sq]
      nlinarith [hsin_pos, norm_nonneg (wz1Cross T.direction U.direction)]
    exact main_cross_proof hδ T U v (Or.inr rfl) θ hθ_pos.le hθ_le hcos hsin_pos hsin_eq
/-- Core covering number bound from slab volume estimates.

If every `t ∈ E` has a slab of width `2W` around `t` containing at least
`V_min` measure of `S`, and the total measure of `S` is at most `V_total`,
then the `rho`-covering number of `E` is bounded by
`(V_total/V_min) * (2W/rho + 2)`.

Proof: take a maximal `2W`-separated subset `I ⊆ E`. The corresponding slabs
are disjoint, so `|I| · V_min ≤ V_total`. Each `2W`-ball can be covered by
`ceil(2W/rho)+1` balls of radius `rho`, giving the bound. -/
lemma covering_number_from_slab_volumes_of_slab_bounds
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {E : Set ℝ} {S : Set X} {W rho V_total V_min : ℝ}
    (proj : X → ℝ)
    (hrho_pos : 0 < rho) (hW_pos : 0 < W) (hVmin_pos : 0 < V_min)
    (hS_meas : MeasurableSet S)
    (hproj_meas : Measurable proj)
    (h_slab : ∀ t ∈ E, μ (S ∩ {x | |proj x - t| ≤ W}) ≥ ENNReal.ofReal V_min)
    (h_total : μ S ≤ ENNReal.ofReal V_total)
    (h_disjoint : ∀ t t', |t - t'| > 2*W →
      Disjoint {x | |proj x - t| ≤ W} {x | |proj x - t'| ≤ W}) :
    (↑(externalCoveringNumber (Real.toNNReal rho) E) : ENNReal) ≤
      ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) := by
  let ε : NNReal := Real.toNNReal (2 * W)
  have hε_pos : 0 < 2 * W := by positivity
  have hε_eq : (ε : ℝ) = 2 * W := by
    simp [ε, Real.toNNReal, hε_pos.le] <;> linarith
  have h_edist : ∀ (t t' : ℝ), (ε : ENNReal) < edist t t' ↔ 2 * W < |t - t'| := by
    intro t t'
    have h1 : edist t t' = ENNReal.ofReal (dist t t') := by simp [edist_dist]
    have h2 : dist t t' = |t - t'| := by simp [Real.dist_eq]
    have hε_ofReal : (ε : ENNReal) = ENNReal.ofReal (2 * W) := by
      rw [← ENNReal.ofReal_coe_nnreal, hε_eq]
    rw [h1, h2, hε_ofReal]
    by_cases h : 0 < |t - t'|
    · rw [ENNReal.ofReal_lt_ofReal_iff h] <;> rfl
    · have h0 : |t - t'| = 0 := by linarith [abs_nonneg (t - t')]
      have hW_nonneg : 0 ≤ W := by linarith
      rw [h0] <;> simp [hε_pos, hW_nonneg]
  let A : ℝ → Set X := fun t => S ∩ {x | |proj x - t| ≤ W}
  have hA_meas : ∀ t : ℝ, MeasurableSet (A t) := by
    intro t
    have h_set_eq : {x : X | |proj x - t| ≤ W} = proj ⁻¹' (Set.Icc (t - W) (t + W)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
      have h_iff : |proj x - t| ≤ W ↔ t - W ≤ proj x ∧ proj x ≤ t + W := by
        rw [abs_le]
        <;> constructor <;> intro h <;> constructor <;> linarith
      exact h_iff
    have h1 : MeasurableSet ({x : X | |proj x - t| ≤ W} : Set X) := by
      rw [h_set_eq]
      exact hproj_meas measurableSet_Icc
    exact hS_meas.inter h1
  -- Step 1: Every finite nonempty ε-separated subset I of E has card ≤ V_total / V_min.
  have h_card_bound : ∀ (I : Finset ℝ), I.Nonempty → (I : Set ℝ) ⊆ E →
      IsSeparated ε (I : Set ℝ) → (I.card : ℝ) ≤ V_total / V_min := by
    intro I hI_nonempty hI hsep
    rcases hI_nonempty with ⟨t0, ht0⟩
    have hVtotal_nonneg : 0 ≤ V_total := by
      have h_pos : 0 < μ (A t0) := by
        have h1 : μ (A t0) ≥ ENNReal.ofReal V_min := h_slab t0 (hI ht0)
        have h2 : 0 < ENNReal.ofReal V_min := ENNReal.ofReal_pos.mpr hVmin_pos
        exact h2.trans_le h1
      have h3 : μ (A t0) ≤ μ S := measure_mono (fun x hx => hx.1)
      have h4 : 0 < μ S := h_pos.trans_le h3
      have h5 : 0 < ENNReal.ofReal V_total := h4.trans_le h_total
      exact (ENNReal.ofReal_pos.mp h5).le
    have h_disj : ∀ t ∈ I, ∀ t' ∈ I, t ≠ t' → Disjoint (A t) (A t') := by
      intro t ht t' ht' hne
      have h_dist : (ε : ENNReal) < edist t t' := hsep ht ht' hne
      have h_dist' : 2 * W < |t - t'| := (h_edist t t').mp h_dist
      have h_slabs_disj : Disjoint {x | |proj x - t| ≤ W} {x | |proj x - t'| ≤ W} :=
        h_disjoint t t' h_dist'
      exact h_slabs_disj.mono (fun _ hx => hx.2) (fun _ hx => hx.2)
    have h_pairwise : (↑I : Set ℝ).PairwiseDisjoint A := by
      intro t ht t' ht' hne
      exact h_disj t ht t' ht' hne
    have h_cover : (⋃ t ∈ I, A t) ⊆ S := by
      intro x hx
      have h_exists : ∃ t ∈ I, x ∈ A t := by
        simpa [Finset.mem_biUnion] using hx
      rcases h_exists with ⟨t, _ht, hxt⟩
      exact hxt.1
    have h_sum : μ (⋃ t ∈ I, A t) = ∑ t ∈ I, μ (A t) :=
      measure_biUnion_finset h_pairwise (fun t _ => hA_meas t)
    have h_lower : ∑ t ∈ I, μ (A t) ≥ (I.card : ENNReal) * ENNReal.ofReal V_min := by
      have h1 : ∀ t ∈ I, μ (A t) ≥ ENNReal.ofReal V_min := by
        intro t ht
        exact h_slab t (hI ht)
      calc
        ∑ t ∈ I, μ (A t) ≥ ∑ t ∈ I, ENNReal.ofReal V_min := Finset.sum_le_sum h1
        _ = (I.card : ENNReal) * ENNReal.ofReal V_min := by
          simp [Finset.sum_const] <;> ring
    have h_total' : μ (⋃ t ∈ I, A t) ≤ ENNReal.ofReal V_total :=
      (measure_mono h_cover).trans h_total
    rw [h_sum] at h_total'
    have h9 : (I.card : ENNReal) * ENNReal.ofReal V_min ≤ ENNReal.ofReal V_total :=
      h_lower.trans h_total'
    have hVmin_nonneg : 0 ≤ V_min := by linarith
    have h9' : (I.card : ENNReal) * ENNReal.ofReal V_min = ENNReal.ofReal ((I.card : ℝ) * V_min) := by
      have h_card : (I.card : ENNReal) = ENNReal.ofReal (I.card : ℝ) := by simp
      rw [h_card, ← ENNReal.ofReal_mul] <;> norm_cast <;> linarith
    rw [h9'] at h9
    have h10 : (I.card : ℝ) * V_min ≤ V_total :=
      (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp h9
    have h11 : (I.card : ℝ) ≤ V_total / V_min := by
      calc
        (I.card : ℝ) = ((I.card : ℝ) * V_min) / V_min := by
          field_simp [hVmin_pos.ne'] <;> ring
        _ ≤ V_total / V_min := by gcongr
    exact h11
  -- Step 2: packingNumber ε E ≠ ⊤.
  let M : ℕ := Nat.ceil (V_total / V_min)
  have h_bound : ∀ (C : Set ℝ), C ⊆ E → IsSeparated ε C → C.encard ≤ (M : ENat) := by
    intro C hC hsepC
    by_cases hC_empty : C = ∅
    · rw [hC_empty]; simp
    · have hC_nonempty : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hC_empty
      by_cases hfin : C.Finite
      · let I := hfin.toFinset
        have hI_eq : (I : Set ℝ) = C := hfin.coe_toFinset
        have hI_nonempty : I.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          have h' : (I : Set ℝ) = ∅ := by simp [h]
          rw [hI_eq] at h'
          exact hC_empty h'
        have h_card : (I.card : ℝ) ≤ V_total / V_min :=
          h_card_bound I hI_nonempty (by simpa [hI_eq] using hC) (by simpa [hI_eq] using hsepC)
        have hI_card_nat : I.card ≤ M := by
          have h : (I.card : ℝ) ≤ (M : ℝ) := by
            calc (I.card : ℝ) ≤ V_total / V_min := h_card
                 _ ≤ (M : ℝ) := Nat.le_ceil _
          exact_mod_cast h
        have h_encard : C.encard = ↑I.card := by
          rw [← hI_eq]
          simp
        rw [h_encard]
        exact_mod_cast hI_card_nat
      · have hinf : C.Infinite := by
          exact Set.not_finite.mp hfin
        exfalso
        rcases hinf.exists_subset_card_eq (M + 1) with ⟨J, hJ, hcard⟩
        have hJ_sep : IsSeparated ε (J : Set ℝ) := hsepC.mono hJ
        have hJ_E : (J : Set ℝ) ⊆ E := hJ.trans hC
        have hJ_nonempty : J.Nonempty := Finset.card_pos.mp (by rw [hcard] <;> simp)
        have h3 : (J.card : ℝ) ≤ V_total / V_min :=
          h_card_bound J hJ_nonempty hJ_E hJ_sep
        rw [hcard] at h3
        have h4 : ((M + 1 : ℕ) : ℝ) ≤ V_total / V_min := h3
        have h5 : ((M + 1 : ℕ) : ℝ) > V_total / V_min := by
          simp [M, Nat.lt_succ_self] <;> linarith [Nat.le_ceil (V_total / V_min)]
        linarith
  have h_main : packingNumber ε E ≤ (M : ENat) := by
    rw [Metric.packingNumber]
    apply iSup_le
    intro C
    apply iSup_le
    intro hC
    apply iSup_le
    intro hsepC
    exact h_bound C hC hsepC
  have h_pack_finite : packingNumber ε E ≠ ⊤ := ne_top_of_le_ne_top (by simp) h_main
  -- Step 3: maximal separated set gives a cover.
  let I : Set ℝ := maximalSeparatedSet ε E
  have hI_subset : I ⊆ E := maximalSeparatedSet_subset
  have hI_sep : IsSeparated ε I := isSeparated_maximalSeparatedSet
  have hI_cover : IsCover ε E I := isCover_maximalSeparatedSet h_pack_finite
  have hI_finite : I.Finite := by
    have h : I.encard ≠ ⊤ := by
      rw [encard_maximalSeparatedSet h_pack_finite] <;> exact h_pack_finite
    by_contra hinf
    have hinf' : I.Infinite := by
      exact Set.not_finite.mp hinf
    have h_top : I.encard = ⊤ := by
      exact Set.encard_eq_top_iff.mpr hinf'
    exact h h_top
  let I' : Finset ℝ := hI_finite.toFinset
  have hI'_eq : (I' : Set ℝ) = I := hI_finite.coe_toFinset
  -- Step 4: refine each 2W-ball to rho-balls.
  let n : ℕ := Nat.ceil (2 * W / rho) + 1
  have hn_bound : (n : ℝ) ≤ 2 * W / rho + 2 := by
    have h : (n : ℝ) = Nat.ceil (2 * W / rho) + 1 := by exact_mod_cast rfl
    rw [h]
    have h2 : (Nat.ceil (2 * W / rho) : ℝ) ≤ 2 * W / rho + 1 := by
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * W / rho)).le
    linarith
  let centers (t : ℝ) : Finset ℝ :=
    Finset.image (fun k : ℕ => t - 2 * W + (2 * (k : ℝ) + 1) * rho) (Finset.range n)
  have h_centers_inj : ∀ (t : ℝ), Function.Injective (fun k : ℕ => t - 2 * W + (2 * (k : ℝ) + 1) * rho) := by
    intro t k1 k2 h
    have h' : (2 * (k1 : ℝ) + 1) * rho = (2 * (k2 : ℝ) + 1) * rho := by linarith
    have h'' : (k1 : ℝ) = (k2 : ℝ) := by
      have h3 : 2 * (k1 : ℝ) + 1 = 2 * (k2 : ℝ) + 1 := by
        apply mul_right_cancel₀ hrho_pos.ne'
        exact h'
      linarith
    exact_mod_cast h''
  let C : Finset ℝ := I'.biUnion centers
  have hC_cover : IsCover (Real.toNNReal rho) E (C : Set ℝ) := by
    intro x hx
    have h_exists_t : ∃ t ∈ I', dist x t ≤ 2 * W := by
      have h_edist_cover : ∃ t ∈ I, edist x t ≤ ε := hI_cover hx
      rcases h_edist_cover with ⟨t, ht, h_ed⟩
      have h_dist : dist x t ≤ (ε : ℝ) := by
        simpa [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)] using h_ed
      have h_t_in_I' : t ∈ I' := by
        have h : t ∈ (I' : Set ℝ) := by
          rw [hI'_eq]
          exact ht
        exact_mod_cast h
      rw [hε_eq] at h_dist
      exact ⟨t, h_t_in_I', h_dist⟩
    rcases h_exists_t with ⟨t, ht, h_dist1⟩
    have h_xdist : |x - t| ≤ 2 * W := by
      simpa [Real.dist_eq] using h_dist1
    have h_xrange1 : t - 2 * W ≤ x := by linarith [abs_le.mp h_xdist]
    have h_xrange2 : x ≤ t + 2 * W := by linarith [abs_le.mp h_xdist]
    set y : ℝ := x - (t - 2 * W) with hy_def
    have hy_nonneg : 0 ≤ y := by linarith
    have hy_le : y ≤ 4 * W := by linarith
    let k : ℕ := Nat.floor (y / (2 * rho))
    have h_y2_nonneg : 0 ≤ y / (2 * rho) := by positivity
    have h_k_le : (k : ℝ) ≤ y / (2 * rho) := Nat.floor_le h_y2_nonneg
    have h_k_gt : y / (2 * rho) < (k : ℝ) + 1 := by
      change y / (2 * rho) < ↑(Nat.floor (y / (2 * rho))) + 1
      exact Nat.lt_floor_add_one (y / (2 * rho))
    have h_k_lt_n : k < n := by
      have h4 : y / (2 * rho) ≤ 2 * W / rho := by
        have h5 : 0 < 2 * rho := by positivity
        have h6 : y / (2 * rho) ≤ (4 * W) / (2 * rho) := by gcongr
        have h7 : (4 * W) / (2 * rho) = 2 * W / rho := by
          field_simp [h5.ne'] <;> ring
        rw [h7] at h6
        exact h6
      have h5 : (k : ℝ) ≤ y / (2 * rho) := Nat.floor_le h_y2_nonneg
      have h6 : (k : ℝ) ≤ 2 * W / rho := by linarith
      have hn_def : (n : ℝ) = (Nat.ceil (2 * W / rho) : ℝ) + 1 := by exact_mod_cast rfl
      have h7 : (k : ℝ) < (n : ℝ) := by
        rw [hn_def]
        have h8 : (k : ℝ) ≤ (Nat.ceil (2 * W / rho) : ℝ) := le_trans h6 (Nat.le_ceil _)
        linarith
      exact_mod_cast h7
    have h_k_in : k ∈ Finset.range n := Finset.mem_range.mpr h_k_lt_n
    let c : ℝ := t - 2 * W + (2 * (k : ℝ) + 1) * rho
    have hc_in : c ∈ centers t := Finset.mem_image.mpr ⟨k, h_k_in, rfl⟩
    have h_dist : |x - c| ≤ rho := by
      dsimp only [c]
      have h5 : -rho ≤ x - (t - 2 * W + (2 * (k : ℝ) + 1) * rho) := by
        have h6 : y ≥ 2 * (k : ℝ) * rho := by
          have h7 : 0 < 2 * rho := by positivity
          calc
            2 * (k : ℝ) * rho
              = (k : ℝ) * (2 * rho) := by ring
            _ ≤ (y / (2 * rho)) * (2 * rho) := by gcongr
            _ = y := by field_simp [h7.ne'] <;> ring
        linarith [hy_def]
      have h7 : x - (t - 2 * W + (2 * (k : ℝ) + 1) * rho) ≤ rho := by
        have h8 : y < (2 * (k : ℝ) + 2) * rho := by
          have h9 : 0 < 2 * rho := by positivity
          calc
            y = (y / (2 * rho)) * (2 * rho) := by field_simp [h9.ne'] <;> ring
            _ < ((k : ℝ) + 1) * (2 * rho) := by gcongr
            _ = (2 * (k : ℝ) + 2) * rho := by ring
        linarith [hy_def]
      exact abs_le.mpr ⟨h5, h7⟩
    have h_c_in_C : c ∈ C := Finset.mem_biUnion.mpr ⟨t, ht, hc_in⟩
    have h_edist : edist x c ≤ (Real.toNNReal rho : ENNReal) := by
      have h_dist' : dist x c ≤ rho := by
        simpa [Real.dist_eq] using h_dist
      have h_ed : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
      rw [h_ed]
      have h_rho : (Real.toNNReal rho : ENNReal) = ENNReal.ofReal rho := by
        have h9 : (Real.toNNReal rho : ℝ) = rho := by
          simp [Real.toNNReal, hrho_pos.le] <;> linarith
        calc
          (Real.toNNReal rho : ENNReal)
            = ENNReal.ofReal (Real.toNNReal rho : ℝ) := by rw [← ENNReal.ofReal_coe_nnreal] <;> rfl
          _ = ENNReal.ofReal rho := by rw [h9]
      rw [h_rho]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    exact ⟨c, h_c_in_C, h_edist⟩
  have hC_card : (C : Set ℝ).encard ≤ (I'.card * n : ENNReal) := by
    have h : C.card ≤ I'.card * n := by
      calc
        C.card ≤ ∑ t ∈ I', (centers t).card := Finset.card_biUnion_le
        _ = ∑ t ∈ I', n := by
          apply Finset.sum_congr rfl
          intro t _
          have h_card_eq : (centers t).card = n := by
            rw [Finset.card_image_of_injective _ (h_centers_inj t)]
            <;> simp [centers]
          exact h_card_eq
        _ = I'.card * n := by simp [Finset.sum_const] <;> ring
    exact_mod_cast h
  have h_main : (↑(externalCoveringNumber (Real.toNNReal rho) E) : ENNReal) ≤ ↑((C : Set ℝ).encard) := by
    exact_mod_cast hC_cover.externalCoveringNumber_le_encard
  by_cases hI'_nonempty : I'.Nonempty
  · rcases hI'_nonempty with ⟨t0, ht0⟩
    have hVtotal_pos : 0 < V_total := by
      have h_t0_in_E : t0 ∈ E := by
        have h_t0_in_I' : t0 ∈ (I' : Set ℝ) := by exact_mod_cast ht0
        have h_t0_in_I : t0 ∈ I := by
          rw [← hI'_eq]
          exact h_t0_in_I'
        exact hI_subset h_t0_in_I
      have h_pos : 0 < μ (A t0) := by
        have h1 : μ (A t0) ≥ ENNReal.ofReal V_min := h_slab t0 h_t0_in_E
        have h2 : 0 < ENNReal.ofReal V_min := ENNReal.ofReal_pos.mpr hVmin_pos
        exact h2.trans_le h1
      have h3 : μ (A t0) ≤ μ S := measure_mono (fun x hx => hx.1)
      have h4 : 0 < μ S := h_pos.trans_le h3
      have h5 : 0 < ENNReal.ofReal V_total := h4.trans_le h_total
      exact ENNReal.ofReal_pos.mp h5
    have hVtotal_nonneg : 0 ≤ V_total := by linarith
    have hI'_nonempty' : I'.Nonempty := ⟨t0, ht0⟩
    have hI_card : (I'.card : ℝ) ≤ V_total / V_min :=
      h_card_bound I' hI'_nonempty' (by simp [hI'_eq, hI_subset]) (by simpa [hI'_eq] using hI_sep)
    have hI_card_nonneg : 0 ≤ (I'.card : ℝ) := by positivity
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    have h_mul : (I'.card : ℝ) * (n : ℝ) ≤ (V_total / V_min) * (2 * W / rho + 2) := by
      nlinarith
    have h_final : (C : Set ℝ).encard ≤ ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) := by
      calc
        (C : Set ℝ).encard ≤ (I'.card * n : ENNReal) := hC_card
        _ = ENNReal.ofReal ((I'.card : ℝ) * (n : ℝ)) := by
          simp <;> norm_cast
        _ ≤ ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) := by
          apply ENNReal.ofReal_le_ofReal
          exact h_mul
    exact h_main.trans h_final
  · have hI'_empty : I' = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using hI'_nonempty
    have hE_empty : E = ∅ := by
      have h1 : ∀ x ∈ E, ∃ t ∈ I, edist x t ≤ ε := by
        simpa [IsCover, SetRel.IsCover] using hI_cover
      have hI_empty : I = ∅ := by
        have h : (I' : Set ℝ) = ∅ := by
          rw [hI'_empty] <;> simp
        exact hI'_eq ▸ h
      have h2 : E ⊆ (∅ : Set ℝ) := by
        intro x hx
        have h3 : ∃ t ∈ I, edist x t ≤ ε := h1 x hx
        rw [hI_empty] at h3
        simp at h3
      exact Set.Subset.antisymm h2 (Set.empty_subset E)
    rw [hE_empty]
    simp
    <;> exact zero_le _

/-- Compatibility wrapper for a projected set equal to the image of `S`. -/
lemma covering_number_from_slab_volumes
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {E : Set ℝ} {S : Set X} {W rho V_total V_min : ℝ}
    (proj : X → ℝ)
    (hrho_pos : 0 < rho) (hW_pos : 0 < W) (hVmin_pos : 0 < V_min)
    (hS_meas : MeasurableSet S)
    (hproj_meas : Measurable proj)
    (hE : E = proj '' S)
    (h_slab : ∀ t ∈ E, μ (S ∩ {x | |proj x - t| ≤ W}) ≥ ENNReal.ofReal V_min)
    (h_total : μ S ≤ ENNReal.ofReal V_total)
    (h_disjoint : ∀ t t', |t - t'| > 2*W →
      Disjoint {x | |proj x - t| ≤ W} {x | |proj x - t'| ≤ W}) :
    (↑(externalCoveringNumber (Real.toNNReal rho) E) : ENNReal) ≤
      ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) := by
  exact covering_number_from_slab_volumes_of_slab_bounds
    proj hrho_pos hW_pos hVmin_pos hS_meas hproj_meas
    h_slab h_total h_disjoint

/-- Transverse fine tube existence from robust close-direction count. -/
lemma transverse_fine_exists
    {delta sigma epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (balanced : WZ1BalancedCoverData
      (sigma := sigma) (epsilon := epsilon) U Y rho)
    (D : ℕ)
    (h_close : ∀ (p : Point3), p ∈ balanced.refined.union →
      ∀ (i : Fin F.card), p ∈ balanced.refined.carrier i →
        (wz1CloseDirectionCount balanced.refined p i rho.1 : ENNReal) ≤
          (D : ENNReal) * Kakeya.realRpowENN (delta / rho.1) (-sigma - epsilon))
    (h_param : (balanced.fineMultiplicity : ENNReal) >
      (D : ENNReal) * Kakeya.realRpowENN (delta / rho.1) (-sigma - epsilon))
    {p : Point3} (hp : p ∈ balanced.refined.union)
    {i : Fin F.card} (hi : p ∈ balanced.refined.carrier i) :
    ∃ (j : Fin F.card), p ∈ balanced.refined.carrier j ∧
      rho.1 ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
  classical
  let A : Finset (Fin F.card) :=
    Finset.univ.filter fun j : Fin F.card => p ∈ balanced.refined.carrier j
  let B : Finset (Fin F.card) :=
    Finset.univ.filter fun j : Fin F.card =>
      p ∈ balanced.refined.carrier j ∧
        ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < rho.1
  have hB_sub_A : B ⊆ A := by
    intro j hj
    simp only [B, A, Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, hj.2.1⟩
  have h_mult : balanced.fineMultiplicity ≤ balanced.refined.pointMultiplicity p :=
    (balanced.fine_constant_multiplicity p hp).1
  have hA_card : A.card = balanced.refined.pointMultiplicity p := by
    have h : balanced.refined.pointMultiplicity p =
        (Finset.univ.filter fun j : Fin F.card => p ∈ balanced.refined.carrier j).card := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      <;> rfl
    exact h.symm
  have hB_card : B.card = wz1CloseDirectionCount balanced.refined p i rho.1 := by
    have h : wz1CloseDirectionCount balanced.refined p i rho.1 =
        (Finset.univ.filter fun j : Fin F.card =>
          p ∈ balanced.refined.carrier j ∧
            ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < rho.1).card := by
      unfold wz1CloseDirectionCount
      <;> rfl
    exact h.symm
  have hB_le : (B.card : ENNReal) ≤
      (D : ENNReal) * Kakeya.realRpowENN (delta / rho.1) (-sigma - epsilon) := by
    rw [hB_card]
    exact h_close p hp i hi
  have h_gt : (B.card : ENNReal) < (balanced.fineMultiplicity : ENNReal) :=
    lt_of_le_of_lt hB_le h_param
  have h_gt_nat : B.card < balanced.fineMultiplicity := by exact_mod_cast h_gt
  have h_A_gt_B : B.card < A.card := by
    rw [hA_card]
    exact h_gt_nat.trans_le h_mult
  have h_diff : (A \ B).Nonempty := by
    have h_disj : Disjoint (A \ B) B := by
      rw [Finset.disjoint_left]
      intro x hx
      have h2 : x ∉ B := (Finset.mem_sdiff.mp hx).2
      exact h2
    have h_union : (A \ B) ∪ B = A := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      <;> tauto
    have h_card : ((A \ B) ∪ B).card = (A \ B).card + B.card :=
      Finset.card_union_of_disjoint h_disj
    have h_sum : (A \ B).card + B.card = A.card := by
      rw [←h_card, h_union]
    have h_pos : 0 < (A \ B).card := by omega
    exact Finset.card_pos.mp h_pos
  rcases h_diff with ⟨j, hj⟩
  have hjA : j ∈ A := (Finset.mem_sdiff.mp hj).1
  have hjB : j ∉ B := (Finset.mem_sdiff.mp hj).2
  have h_active : p ∈ balanced.refined.carrier j := by
    simp only [A, Finset.mem_filter] at hjA
    exact hjA.2
  have h_cross : rho.1 ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
    by_contra h
    have h9 : ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < rho.1 := by linarith
    have h10 : j ∈ B := by
      simp only [B, Finset.mem_filter]
      exact ⟨Finset.mem_univ j, h_active, h9⟩
    exact hjB h10
  exact ⟨j, h_active, h_cross⟩

end Kakeya.Assouad
