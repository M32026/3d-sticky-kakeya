import MyLeanRepo.Kakeya.Assouad.IntersectionDiameterBounds
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Volume upper bound for the intersection of two misaligned δ-tubes

If two δ-tubes meet at angle θ with `sin θ ≥ 32δ`, their intersection has
volume at most half the volume of one tube.
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Assouad

/--
Volume of a set bounded by the product of three coordinate diameters
after applying a linear isometry.
-/
private lemma volume_by_three_diameters {E : Set Point3} (hE : MeasurableSet E)
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
    have hz_eq : z = F (A w) := h_eq1.symm.trans (congr_arg F h_eq2.symm)
    have hz'_eq : z' = F (A w') := h_eq1'.symm.trans (congr_arg F h_eq2'.symm)
    have h_goal : dist (z 0) (z' 0) = |(A w) 0 - (A w') 0| := by
      rw [hz_eq, hz'_eq, Real.dist_eq] <;> rfl
    rw [h_goal]
    exact h
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
    have hz_eq : z = F (A w) := h_eq1.symm.trans (congr_arg F h_eq2.symm)
    have hz'_eq : z' = F (A w') := h_eq1'.symm.trans (congr_arg F h_eq2'.symm)
    have h_goal : dist (z 1) (z' 1) = |(A w) 1 - (A w') 1| := by
      rw [hz_eq, hz'_eq, Real.dist_eq] <;> rfl
    rw [h_goal]
    exact h
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
    have hz_eq : z = F (A w) := h_eq1.symm.trans (congr_arg F h_eq2.symm)
    have hz'_eq : z' = F (A w') := h_eq1'.symm.trans (congr_arg F h_eq2'.symm)
    have h_goal : dist (z 2) (z' 2) = |(A w) 2 - (A w') 2| := by
      rw [hz_eq, hz'_eq, Real.dist_eq] <;> rfl
    rw [h_goal]
    exact h
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
Volume upper bound for the intersection of two misaligned δ-tubes.

If `sin θ ≥ 32δ`, the intersection volume is at most half of one tube's volume.
-/
lemma misaligned_tubes_intersection_volume_upper {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000)
    (T U : Kakeya.DeltaTube δ)
    (v : Point3) (h_v_choice : v = U.direction ∨ v = -U.direction)
    (θ : ℝ) (hθ_nonneg : 0 ≤ θ) (hθ_le : θ ≤ Real.pi / 2)
    (hcos : inner ℝ T.direction v = Real.cos θ)
    (hsin_pos : 0 < Real.sin θ)
    (hsin_large : 32 * δ ≤ Real.sin θ) :
    MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
      (2 : ENNReal)⁻¹ * T.volume := by
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
  have harith : d0 * d1 * d2 ≤ δ ^ 2 / 2 := by
    rw [h_expr]
    have hsin : 0 < Real.sin θ := hsin_pos
    have h' : 1 + Real.cos θ ≤ 2 := by linarith [Real.cos_le_one θ]
    have h : 8 * δ ^ 3 * (1 + Real.cos θ) ≤ 16 * δ ^ 3 := by
      calc
        8 * δ ^ 3 * (1 + Real.cos θ) ≤ 8 * δ ^ 3 * 2 := by gcongr
        _ = 16 * δ ^ 3 := by ring
    have hstep1 : 8 * δ ^ 3 * (1 + Real.cos θ) / Real.sin θ ≤ 16 * δ ^ 3 / Real.sin θ :=
      div_le_div_of_nonneg_right h hsin.le
    have h4 : 16 * δ ^ 3 ≤ (δ ^ 2 / 2) * Real.sin θ := by
      have h5 : (δ ^ 2 / 2) * (32 * δ) = 16 * δ ^ 3 := by ring
      rw [← h5]
      exact mul_le_mul_of_nonneg_left hsin_large (by positivity)
    have hstep2 : 16 * δ ^ 3 / Real.sin θ ≤ δ ^ 2 / 2 := by
      have hdiv : 16 * δ ^ 3 / Real.sin θ ≤ ((δ ^ 2 / 2) * Real.sin θ) / Real.sin θ :=
        div_le_div_of_nonneg_right h4 hsin.le
      have hfinal : ((δ ^ 2 / 2) * Real.sin θ) / Real.sin θ = δ ^ 2 / 2 := by
        field_simp [hsin.ne'] <;> ring
      exact hdiv.trans (le_of_eq hfinal)
    exact hstep1.trans hstep2
  have hfinal : volume S ≤ ENNReal.ofReal (δ ^ 2 / 2) :=
    hvol_bound.trans (ENNReal.ofReal_le_ofReal harith)
  have hT_lower : ENNReal.ofReal (δ ^ 2) ≤ T.volume :=
    tube_volume_lower_bound hδ (by linarith) T
  have hhalf : ENNReal.ofReal (δ ^ 2 / 2) = (2 : ENNReal)⁻¹ * ENNReal.ofReal (δ ^ 2) := by
    have h : ENNReal.ofReal (δ ^ 2 / 2) = ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ 2) := by ring_nf
    rw [h]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / 2)] <;> simp
  rw [hhalf] at hfinal
  have h_apply : (2 : ENNReal)⁻¹ * ENNReal.ofReal (δ ^ 2) ≤ (2 : ENNReal)⁻¹ * T.volume :=
    mul_le_mul_right hT_lower (2 : ENNReal)⁻¹
  exact hfinal.trans h_apply

end Kakeya.Assouad
