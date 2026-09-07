import MyLeanRepo.Kakeya.Assouad.IntersectionDiameterBounds
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Hairbrush geometric helper lemmas

Tasks:
1. Tube intersection volume at angle θ: volume ≤ C * δ³ / sin θ
2. 2-plane neighborhood containment
3. Direction packing from Frostman slab bound
4. 2-plane tube count from KatzTao bound
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/--
Volume of a set bounded by the product of three coordinate diameters
after applying a linear isometry.
-/
lemma volume_by_three_diameters {E : Set Point3} (hE : MeasurableSet E)
    (A : Point3 ≃ₗᵢ[ℝ] Point3)
    (d0 d1 d2 : ℝ) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2)
    (h0 : ∀ x y, x ∈ E → y ∈ E → |(A x) 0 - (A y) 0| ≤ d0)
    (h1 : ∀ x y, x ∈ E → y ∈ E → |(A x) 1 - (A y) 1| ≤ d1)
    (h2 : ∀ x y, x ∈ E → y ∈ E → |(A x) 2 - (A y) 2| ≤ d2) :
    volume E ≤ ENNReal.ofReal (d0 * d1 * d2) := by
  let AS : Set Point3 := A '' E
  let F : Point3 → (Fin 3 → ℝ) := WithLp.ofLp (p := 2)
  let AS' : Set (Fin 3 → ℝ) := F '' AS
  have hpres_F : MeasurePreserving F volume volume := PiLp.volume_preserving_ofLp (ι := Fin 3)
  have hcontG : Continuous (WithLp.toLp (p := 2) : (Fin 3 → ℝ) → Point3) :=
    PiLp.continuous_toLp 2 (β := fun (_ : Fin 3) => ℝ)
  let F_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := F
      invFun := WithLp.toLp (p := 2)
      left_inv := WithLp.toLp_ofLp (p := 2)
      right_inv := WithLp.ofLp_toLp (p := 2)
      measurable_toFun := hpres_F.measurable
      measurable_invFun := hcontG.measurable }
  have hAS_meas : MeasurableSet AS :=
    A.toMeasurableEquiv.measurableSet_image.mpr hE
  have hAS'_eq : F_equiv '' AS = AS' := by rfl
  have hAS'_meas : MeasurableSet AS' := by
    rw [← hAS'_eq]
    exact F_equiv.measurableSet_image.mpr hAS_meas
  have hvol : volume E = volume AS := by
    have hpres : MeasurePreserving A volume volume := A.measurePreserving
    have hmap : Measure.map A volume = volume := hpres.map_eq
    have h : volume AS = Measure.map A volume AS := by rw [hmap]
    rw [h]
    have h2 : Measure.map A volume AS = volume (A ⁻¹' AS) :=
      Measure.map_apply hpres.measurable hAS_meas
    rw [h2]
    have h3 : A ⁻¹' AS = E := by
      rw [show AS = A '' E from rfl]
      rw [Set.preimage_image_eq _ A.injective]
    rw [h3]
  have hF_inj : Function.Injective F := by
    intro x y h
    exact F_equiv.injective h
  have hvol' : volume AS' = volume AS := by
    have hmap : Measure.map F volume = volume := hpres_F.map_eq
    calc
      volume AS'
        = Measure.map F volume AS' := by rw [hmap]
      _ = volume (F ⁻¹' AS') := Measure.map_apply hpres_F.measurable hAS'_meas
      _ = volume AS := by rw [Set.preimage_image_eq _ hF_inj]
  have hmain : volume AS' ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' AS') :=
    Real.volume_pi_le_prod_diam AS'
  have h_ediam0 : Metric.ediam (Function.eval 0 '' AS') ≤ ENNReal.ofReal d0 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rcases ha with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, h_eq1⟩
    rcases hx with ⟨w, hw, h_eq2⟩
    rcases hb with ⟨z', hz', rfl⟩
    rcases hz' with ⟨y, hy, h_eq1'⟩
    rcases hy with ⟨w', hw', h_eq2'⟩
    have h : |(A w) 0 - (A w') 0| ≤ d0 := h0 w w' hw hw'
    have hz_eq : z = F (A w) := by
      calc z = F x := h_eq1.symm
           _ = F (A w) := by rw [h_eq2.symm]
    have hz'_eq : z' = F (A w') := by
      calc z' = F y := h_eq1'.symm
           _ = F (A w') := by rw [h_eq2'.symm]
    have h_goal : dist (z 0) (z' 0) = |(A w) 0 - (A w') 0| := by
      rw [hz_eq, hz'_eq, Real.dist_eq] <;> rfl
    rw [h_goal]; exact h
  have h_ediam1 : Metric.ediam (Function.eval 1 '' AS') ≤ ENNReal.ofReal d1 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rcases ha with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, h_eq1⟩
    rcases hx with ⟨w, hw, h_eq2⟩
    rcases hb with ⟨z', hz', rfl⟩
    rcases hz' with ⟨y, hy, h_eq1'⟩
    rcases hy with ⟨w', hw', h_eq2'⟩
    have h : |(A w) 1 - (A w') 1| ≤ d1 := h1 w w' hw hw'
    have hz_eq : z = F (A w) := by
      calc z = F x := h_eq1.symm
           _ = F (A w) := by rw [h_eq2.symm]
    have hz'_eq : z' = F (A w') := by
      calc z' = F y := h_eq1'.symm
           _ = F (A w') := by rw [h_eq2'.symm]
    have h_goal : dist (z 1) (z' 1) = |(A w) 1 - (A w') 1| := by
      rw [hz_eq, hz'_eq, Real.dist_eq] <;> rfl
    rw [h_goal]; exact h
  have h_ediam2 : Metric.ediam (Function.eval 2 '' AS') ≤ ENNReal.ofReal d2 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rcases ha with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, h_eq1⟩
    rcases hx with ⟨w, hw, h_eq2⟩
    rcases hb with ⟨z', hz', rfl⟩
    rcases hz' with ⟨y, hy, h_eq1'⟩
    rcases hy with ⟨w', hw', h_eq2'⟩
    have h : |(A w) 2 - (A w') 2| ≤ d2 := h2 w w' hw hw'
    have hz_eq : z = F (A w) := by
      calc z = F x := h_eq1.symm
           _ = F (A w) := by rw [h_eq2.symm]
    have hz'_eq : z' = F (A w') := by
      calc z' = F y := h_eq1'.symm
           _ = F (A w') := by rw [h_eq2'.symm]
    have h_goal : dist (z 2) (z' 2) = |(A w) 2 - (A w') 2| := by
      rw [hz_eq, hz'_eq, Real.dist_eq] <;> rfl
    rw [h_goal]; exact h
  have hprod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' AS')) ≤
      ENNReal.ofReal (d0 * d1 * d2) := by
    have h_expand : (∏ i : Fin 3, Metric.ediam (Function.eval i '' AS')) =
        Metric.ediam (Function.eval 0 '' AS') *
        Metric.ediam (Function.eval 1 '' AS') *
        Metric.ediam (Function.eval 2 '' AS') := by
      simp [Fin.prod_univ_succ] <;> ring
    rw [h_expand]
    have hmul : ENNReal.ofReal d0 * ENNReal.ofReal d1 * ENNReal.ofReal d2 =
        ENNReal.ofReal (d0 * d1 * d2) := by
      rw [← ENNReal.ofReal_mul hd0, ← ENNReal.ofReal_mul (mul_nonneg hd0 hd1)] <;> ring
    rw [← hmul]
    gcongr
  calc
    volume E = volume AS := hvol
    _ = volume AS' := hvol'.symm
    _ ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' AS') := hmain
    _ ≤ ENNReal.ofReal (d0 * d1 * d2) := hprod

/--
Task 1: Tube intersection volume at angle θ.

For two δ-tubes T, U whose directions make angle θ (with sin θ > 0),
the intersection volume is at most `16 * δ³ / sin θ`.

This is the sharp scaling needed for the hairbrush volume estimate.
-/
lemma tube_intersection_volume_angle
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000)
    (T U : Kakeya.DeltaTube δ)
    (v : Point3) (h_v_choice : v = U.direction ∨ v = -U.direction)
    (θ : ℝ) (hθ_nonneg : 0 ≤ θ) (hθ_le : θ ≤ Real.pi / 2)
    (hcos : inner ℝ T.direction v = Real.cos θ)
    (hsin_pos : 0 < Real.sin θ) :
    MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
      ENNReal.ofReal (16 * δ ^ 3 / Real.sin θ) := by
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
  have he2_orth_U : inner ℝ U.direction e2 = 0 := by
    have h_comm : inner ℝ U.direction e2 = inner ℝ e2 U.direction :=
      (real_inner_comm U.direction e2).symm
    rw [h_comm]
    cases h_v_choice with
    | inl h =>
      have hU : U.direction = v := h.symm
      rw [hU]
      have h : inner ℝ e2 v = inner ℝ (A e2) (A v) := (A.inner_map_map e2 v).symm
      rw [h, hA_e2, hA]
      have h_zero : inner ℝ e1_std e0_std = 0 := by
        have h := EuclideanSpace.inner_single_right 0 (1 : ℝ) e1_std
        simpa [e0_std, e1_std, EuclideanSpace.single_apply] using h
      exact h_zero
    | inr h =>
      have hU : U.direction = -v := neg_eq_iff_eq_neg.mp h.symm
      rw [hU, inner_neg_right]
      have h : inner ℝ e2 v = inner ℝ (A e2) (A v) := (A.inner_map_map e2 v).symm
      rw [h, hA_e2, hA]
      have h_zero : inner ℝ e1_std e0_std = 0 := by
        have h := EuclideanSpace.inner_single_right 0 (1 : ℝ) e1_std
        simpa [e0_std, e1_std, EuclideanSpace.single_apply] using h
      simpa using h_zero
  have he3_orth_U : inner ℝ U.direction e3 = 0 := by
    have h_comm : inner ℝ U.direction e3 = inner ℝ e3 U.direction :=
      (real_inner_comm U.direction e3).symm
    rw [h_comm]
    cases h_v_choice with
    | inl h =>
      have hU : U.direction = v := h.symm
      rw [hU]
      have h : inner ℝ e3 v = inner ℝ (A e3) (A v) := (A.inner_map_map e3 v).symm
      rw [h, hA_e3, hA]
      have h_zero : inner ℝ e2_std e0_std = 0 := by
        have h := EuclideanSpace.inner_single_right 0 (1 : ℝ) e2_std
        simpa [e0_std, e2_std, EuclideanSpace.single_apply] using h
      exact h_zero
    | inr h =>
      have hU : U.direction = -v := neg_eq_iff_eq_neg.mp h.symm
      rw [hU, inner_neg_right]
      have h : inner ℝ e3 v = inner ℝ (A e3) (A v) := (A.inner_map_map e3 v).symm
      rw [h, hA_e3, hA]
      have h_zero : inner ℝ e2_std e0_std = 0 := by
        have h := EuclideanSpace.inner_single_right 0 (1 : ℝ) e2_std
        simpa [e0_std, e2_std, EuclideanSpace.single_apply] using h
      simpa using h_zero
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
  have hcos_nonneg : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ_le⟩
  have hd0_nonneg : 0 ≤ d0 := by
    dsimp only [d0]; apply div_nonneg
    · have h : 0 ≤ 2 * δ * (1 + Real.cos θ) := by positivity
      exact h
    · exact hsin_pos.le
  have hd1_nonneg : 0 ≤ d1 := by positivity
  have hd2_nonneg : 0 ≤ d2 := by positivity
  have hS_meas : MeasurableSet S := by
    have hT_comp : IsCompact T.carrier := (isCompact_Icc.image (by fun_prop)).cthickening
    have hU_comp : IsCompact U.carrier := (isCompact_Icc.image (by fun_prop)).cthickening
    exact (hT_comp.inter_right hU_comp.isClosed).measurableSet
  have h0 : ∀ x y, x ∈ S → y ∈ S → |(A x) 0 - (A y) 0| ≤ d0 := by
    intro x y hx hy
    rw [hcoord0 x, hcoord0 y]
    have h : inner ℝ x v - inner ℝ y v = inner ℝ (x - y) v := by
      rw [inner_sub_left]
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
      rw [h_eq]
      exact abs_sub _ _
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
      rw [h_eq]
      exact abs_sub _ _
    linarith
  have hvol_bound : volume S ≤ ENNReal.ofReal (d0 * d1 * d2) :=
    volume_by_three_diameters hS_meas A d0 d1 d2 hd0_nonneg hd1_nonneg hd2_nonneg h0 h1 h2
  have h_expr : d0 * d1 * d2 = 8 * δ ^ 3 * (1 + Real.cos θ) / Real.sin θ := by
    dsimp only [d0, d1, d2] <;> ring
  have hcos_le_one : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have h_arith : 8 * δ ^ 3 * (1 + Real.cos θ) / Real.sin θ ≤ 16 * δ ^ 3 / Real.sin θ := by
    have h' : 1 + Real.cos θ ≤ 2 := by linarith
    have h : 8 * δ ^ 3 * (1 + Real.cos θ) ≤ 16 * δ ^ 3 := by
      calc
        8 * δ ^ 3 * (1 + Real.cos θ) ≤ 8 * δ ^ 3 * 2 := by gcongr
        _ = 16 * δ ^ 3 := by ring
    have hsin : 0 < Real.sin θ := hsin_pos
    exact div_le_div_of_nonneg_right h hsin.le
  rw [h_expr] at hvol_bound
  exact hvol_bound.trans (ENNReal.ofReal_le_ofReal h_arith)

/--
Katz-Tao count bound for a convex set of volume O(σ·δ).

If `W` is convex with `volume W ≤ C · σ · δ`, and the family satisfies the
Katz-Tao convex Wolff bound with constant `C_KT`, then the number of tubes
contained in `W` is at most `C_KT · C · σ / δ`.

This gives the standard 2-plane tube count: tubes lying in a thin slab around
a 2-plane and within a σ-length region occupy a convex set of volume ~σ·δ,
and since each tube has volume ≥ δ², the count is ~σ/δ.
-/
lemma katzTao_convex_volume_count {δ : ℝ} (hδ : 0 < δ)
    {σ : ℝ} (hσ : 0 < σ)
    (F : Kakeya.TubeFamily δ)
    {C_KT C : ℝ} (hC_KT_nonneg : 0 ≤ C_KT) (hC_nonneg : 0 ≤ C)
    (hKT : Kakeya.KatzTaoConvexWolffBound F C_KT)
    (W : Set Point3) (hW_convex : Convex ℝ W)
    (hVol : volume W ≤ ENNReal.ofReal (C * σ * δ)) :
    F.containedCount W ≤
      ENNReal.ofReal (C_KT * C) * ENNReal.ofReal σ * (ENNReal.ofReal δ)⁻¹ := by
  have h1 : F.containedCount W ≤
      ENNReal.ofReal C_KT * volume W * (Kakeya.deltaTubeVolume δ)⁻¹ :=
    hKT W hW_convex
  have hTube_lower : ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
    canonical_volume_lower hδ
  have h2 : (Kakeya.deltaTubeVolume δ)⁻¹ ≤ (ENNReal.ofReal (δ ^ 2))⁻¹ :=
    ENNReal.inv_le_inv.mpr hTube_lower
  have hδ_pos' : 0 < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  have hδ_ne_zero : ENNReal.ofReal δ ≠ 0 := hδ_pos'.ne'
  have hδ_ne_top : ENNReal.ofReal δ ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    F.containedCount W
      ≤ ENNReal.ofReal C_KT * volume W * (Kakeya.deltaTubeVolume δ)⁻¹ := h1
    _ ≤ ENNReal.ofReal C_KT * ENNReal.ofReal (C * σ * δ) * (ENNReal.ofReal (δ ^ 2))⁻¹ := by
      gcongr <;> assumption
    _ = ENNReal.ofReal (C_KT * C) * ENNReal.ofReal σ * (ENNReal.ofReal δ)⁻¹ := by
      have hCσ : 0 ≤ C * σ := mul_nonneg hC_nonneg hσ.le
      have h_expand : ENNReal.ofReal (C * σ * δ) =
          ENNReal.ofReal C * ENNReal.ofReal σ * ENNReal.ofReal δ := by
        have h1 : ENNReal.ofReal (C * σ) = ENNReal.ofReal C * ENNReal.ofReal σ :=
          ENNReal.ofReal_mul hC_nonneg
        have h2 : ENNReal.ofReal ((C * σ) * δ) =
            ENNReal.ofReal (C * σ) * ENNReal.ofReal δ :=
          ENNReal.ofReal_mul hCσ
        have h3 : (C * σ) * δ = C * σ * δ := by ring
        rw [h3] at h2
        rw [h2, h1] <;> ring
      have h_pow2 : ENNReal.ofReal (δ ^ 2) = ENNReal.ofReal δ * ENNReal.ofReal δ := by
        rw [pow_two, ENNReal.ofReal_mul hδ.le]
      have h_inv : (ENNReal.ofReal δ * ENNReal.ofReal δ)⁻¹ =
          (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ)⁻¹ :=
        ENNReal.mul_inv (Or.inl hδ_ne_zero) (Or.inl hδ_ne_top)
      have h_cancel : ENNReal.ofReal δ * ((ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ)⁻¹) =
          (ENNReal.ofReal δ)⁻¹ := by
        have h9 : ENNReal.ofReal δ * (ENNReal.ofReal δ)⁻¹ = 1 :=
          ENNReal.mul_inv_cancel hδ_ne_zero hδ_ne_top
        rw [←mul_assoc, h9, one_mul]
      have h5 : ENNReal.ofReal C_KT * ENNReal.ofReal C = ENNReal.ofReal (C_KT * C) := by
        rw [←ENNReal.ofReal_mul hC_KT_nonneg] <;> ring
      calc
        ENNReal.ofReal C_KT * ENNReal.ofReal (C * σ * δ) * (ENNReal.ofReal (δ ^ 2))⁻¹
          = ENNReal.ofReal C_KT * (ENNReal.ofReal C * ENNReal.ofReal σ * ENNReal.ofReal δ) *
              ((ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ)⁻¹) := by
            rw [h_expand, h_pow2, h_inv]
        _ = (ENNReal.ofReal C_KT * ENNReal.ofReal C) * ENNReal.ofReal σ *
              (ENNReal.ofReal δ * ((ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ)⁻¹)) := by
            simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
        _ = (ENNReal.ofReal C_KT * ENNReal.ofReal C) * ENNReal.ofReal σ * (ENNReal.ofReal δ)⁻¹ := by
            rw [h_cancel]
        _ = ENNReal.ofReal (C_KT * C) * ENNReal.ofReal σ * (ENNReal.ofReal δ)⁻¹ := by
            rw [h5]

/--
2-plane neighborhood containment.

Let `Π` be the affine 2-plane through `T.base` whose direction space is spanned
by `T.direction` and `U.direction`. If `T.carrier` and `U.carrier` intersect,
then `U.carrier` is contained in the `3δ`-neighborhood of `Π`.

We state this in terms of a unit normal `n` to the plane: for every `z ∈ U.carrier`,
the normal component `|inner(z - T.base, n)|` is at most `3δ`.

The angle condition is not needed for this bound; it only ensures the plane is
well-defined (directions not parallel).
-/
lemma two_plane_neighborhood_containment {δ : ℝ} (hδ : 0 < δ)
    (T U : Kakeya.DeltaTube δ)
    (n : Point3) (hn_unit : ‖n‖ = 1)
    (hn_perp_T : inner ℝ T.direction n = 0)
    (hn_perp_U : inner ℝ U.direction n = 0)
    (h_inter : (T.carrier ∩ U.carrier).Nonempty) :
    ∀ z ∈ U.carrier, |inner ℝ (z - T.base) n| ≤ 3 * δ := by
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h_contT : Continuous (fun t : ℝ => T.base + t • T.direction) := by continuity
  have h_contU : Continuous (fun t : ℝ => U.base + t • U.direction) := by continuity
  have h_segT_closed : IsClosed (Kakeya.unitSegment T.base T.direction) :=
    (isCompact_Icc.image h_contT).isClosed
  have h_segU_closed : IsClosed (Kakeya.unitSegment U.base U.direction) :=
    (isCompact_Icc.image h_contU).isClosed
  let segT := Kakeya.unitSegment T.base T.direction
  let segU := Kakeya.unitSegment U.base U.direction
  have h_thick_T : T.carrier = ⋃ y ∈ segT, Metric.closedBall y δ := by
    have h1 : T.carrier = Metric.cthickening δ segT := by rfl
    rw [h1]
    have h2 := Metric.cthickening_eq_biUnion_closedBall segT hδ_nonneg
    rw [h2, h_segT_closed.closure_eq]
  have h_thick_U : U.carrier = ⋃ y ∈ segU, Metric.closedBall y δ := by
    have h1 : U.carrier = Metric.cthickening δ segU := by rfl
    rw [h1]
    have h2 := Metric.cthickening_eq_biUnion_closedBall segU hδ_nonneg
    rw [h2, h_segU_closed.closure_eq]
  rcases h_inter with ⟨x, hx⟩
  have hxT : x ∈ T.carrier := hx.1
  have hxU : x ∈ U.carrier := hx.2
  have hxT' : x ∈ (⋃ y ∈ segT, Metric.closedBall y δ) := by
    simpa [h_thick_T] using hxT
  have hxU' : x ∈ (⋃ y ∈ segU, Metric.closedBall y δ) := by
    simpa [h_thick_U] using hxU
  rcases Set.mem_iUnion₂.mp hxT' with ⟨a, ha_seg, hxa_ball⟩
  rcases Set.mem_iUnion₂.mp hxU' with ⟨b, hb_seg, hxb_ball⟩
  have hxa_dist : dist x a ≤ δ := by simpa [Metric.mem_closedBall] using hxa_ball
  have hxb_dist : dist x b ≤ δ := by simpa [Metric.mem_closedBall] using hxb_ball
  rcases ha_seg with ⟨s, hs, h_eq_a⟩
  rcases hb_seg with ⟨t, ht, h_eq_b⟩
  have h_inner_a : inner ℝ (a - T.base) n = 0 := by
    have h_vec : a - T.base = s • T.direction := by
      have h : a = T.base + s • T.direction := h_eq_a.symm
      rw [h]
      simp
    rw [h_vec]
    have h2 : inner ℝ (s • T.direction) n = s * inner ℝ T.direction n := by
      exact real_inner_smul_left T.direction n s
    rw [h2, hn_perp_T] <;> ring
  have h1 : |inner ℝ (x - T.base) n| ≤ δ := by
    have h_eq : inner ℝ (x - T.base) n = inner ℝ (x - a) n := by
      have h : x - T.base = (x - a) + (a - T.base) := by abel
      rw [h, inner_add_left, h_inner_a, add_zero]
    rw [h_eq]
    have h2 : |inner ℝ (x - a) n| ≤ ‖x - a‖ * ‖n‖ := abs_real_inner_le_norm (x - a) n
    rw [hn_unit] at h2
    have h3 : ‖x - a‖ ≤ δ := by simpa [dist_eq_norm] using hxa_dist
    linarith
  have h_const_b : inner ℝ (b - T.base) n = inner ℝ (U.base - T.base) n := by
    have h_vec : b - T.base = (U.base - T.base) + t • U.direction := by
      have h : b = U.base + t • U.direction := h_eq_b.symm
      rw [h]
      simp [sub_add_eq_add_sub]
      <;> abel
    rw [h_vec]
    have h21 : inner ℝ ((U.base - T.base) + t • U.direction) n =
        inner ℝ (U.base - T.base) n + inner ℝ (t • U.direction) n := by
      rw [inner_add_left]
    rw [h21]
    have h22 : inner ℝ (t • U.direction) n = t * inner ℝ U.direction n := by
      rw [inner_smul_left_eq_smul U.direction n t]
      <;> rfl
    rw [h22, hn_perp_U] <;> ring
  have h3 : |inner ℝ (U.base - T.base) n| ≤ 2 * δ := by
    rw [←h_const_b]
    have h4 : inner ℝ (b - T.base) n = inner ℝ (x - T.base) n - inner ℝ (x - b) n := by
      have h5 : x - T.base = (b - T.base) + (x - b) := by abel
      have h6 : inner ℝ (x - T.base) n = inner ℝ (b - T.base) n + inner ℝ (x - b) n := by
        rw [h5, inner_add_left]
      linarith
    rw [h4]
    have h6 : |inner ℝ (x - b) n| ≤ δ := by
      have h7 : |inner ℝ (x - b) n| ≤ ‖x - b‖ * ‖n‖ := abs_real_inner_le_norm (x - b) n
      rw [hn_unit] at h7
      have h8 : ‖x - b‖ ≤ δ := by simpa [dist_eq_norm] using hxb_dist
      linarith
    have h9 : |inner ℝ (x - T.base) n - inner ℝ (x - b) n| ≤
        |inner ℝ (x - T.base) n| + |inner ℝ (x - b) n| := by
      exact abs_sub _ _
    linarith
  intro z hz
  have hz' : z ∈ (⋃ y ∈ segU, Metric.closedBall y δ) := by
    simpa [h_thick_U] using hz
  rcases Set.mem_iUnion₂.mp hz' with ⟨c, hc_seg, hzc_ball⟩
  have hzc_dist : dist z c ≤ δ := by simpa [Metric.mem_closedBall] using hzc_ball
  rcases hc_seg with ⟨r, hr, h_eq_c⟩
  have h_const_c : inner ℝ (c - T.base) n = inner ℝ (U.base - T.base) n := by
    have h_vec : c - T.base = (U.base - T.base) + r • U.direction := by
      have h : c = U.base + r • U.direction := h_eq_c.symm
      rw [h]
      simp [sub_add_eq_add_sub]
      <;> abel
    rw [h_vec]
    have h21 : inner ℝ ((U.base - T.base) + r • U.direction) n =
        inner ℝ (U.base - T.base) n + inner ℝ (r • U.direction) n := by
      rw [inner_add_left]
    rw [h21]
    have h22 : inner ℝ (r • U.direction) n = r * inner ℝ U.direction n := by
      rw [inner_smul_left_eq_smul U.direction n r]
      <;> rfl
    rw [h22, hn_perp_U] <;> ring
  have h9 : inner ℝ (z - T.base) n = inner ℝ (z - c) n + inner ℝ (c - T.base) n := by
    have h10 : z - T.base = (z - c) + (c - T.base) := by abel
    rw [h10, inner_add_left]
  rw [h9, h_const_c]
  have h11 : |inner ℝ (z - c) n| ≤ δ := by
    have h12 : |inner ℝ (z - c) n| ≤ ‖z - c‖ * ‖n‖ := abs_real_inner_le_norm (z - c) n
    rw [hn_unit] at h12
    have h13 : ‖z - c‖ ≤ δ := by simpa [dist_eq_norm] using hzc_dist
    linarith
  have h14 : |inner ℝ (z - c) n + inner ℝ (U.base - T.base) n| ≤
      |inner ℝ (z - c) n| + |inner ℝ (U.base - T.base) n| := by
    exact abs_add_le _ _
  linarith

end Kakeya.Assouad
