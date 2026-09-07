import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Hairbrush.TwoDKakeya
import MyLeanRepo.Kakeya.Assouad.IntersectionDiameterBounds
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Hairbrush.Basic
import MyLeanRepo.Kakeya.Hairbrush.Helpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Intersection sum bound for 2D Kakeya

Dyadic angle decomposition: ∑_{U ≠ T} |Y(T) ∩ Y(U)| ≤ C * V * log(1/δ)
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Hairbrush

variable {δ : ℝ} {F : Kakeya.TubeFamily δ} {Y : Kakeya.Shading F}

local instance : DecidableEq (Kakeya.DeltaTube δ) := Classical.decEq _

/-- Effective angle in [0, π/2]. -/
def effectiveAngle {δ : ℝ} (T U : Kakeya.DeltaTube δ) : ℝ :=
  min (angleBetween T U) (Real.pi - angleBetween T U)

lemma effectiveAngle_nonneg {δ : ℝ} (T U : Kakeya.DeltaTube δ) :
    0 ≤ effectiveAngle T U := by
  dsimp only [effectiveAngle]
  have h1 : 0 ≤ angleBetween T U := Real.arccos_nonneg _
  have h2 : 0 ≤ Real.pi - angleBetween T U := by
    have h3 : angleBetween T U ≤ Real.pi := Real.arccos_le_pi _
    linarith [Real.pi_pos]
  exact le_min_iff.mpr ⟨h1, h2⟩

lemma effectiveAngle_le_pi2 {δ : ℝ} (T U : Kakeya.DeltaTube δ) :
    effectiveAngle T U ≤ Real.pi / 2 := by
  dsimp only [effectiveAngle]
  by_cases h : angleBetween T U ≤ Real.pi / 2
  · exact min_le_iff.mpr (Or.inl h)
  · have h' : Real.pi - angleBetween T U ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    exact min_le_iff.mpr (Or.inr h')

/-- All directions within C₀δ of plane perpendicular to n. -/
def LiesInTwoPlaneNeighborhood {δ : ℝ} (F : Kakeya.TubeFamily δ)
    (n : Point3) (C0 : ℝ) : Prop :=
  ‖n‖ = 1 ∧ ∀ T ∈ F, |inner ℝ T.direction n| ≤ C0 * δ

/-- sin θ ≥ 2θ/π for θ ∈ [0, π/2]. -/
lemma sin_lower_bound {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    Real.sin θ ≥ 2 * θ / Real.pi := by
  have h : (2 / Real.pi) * θ ≤ Real.sin θ := Real.mul_le_sin h0 h1
  have h' : (2 / Real.pi) * θ = 2 * θ / Real.pi := by ring
  rw [h'] at h; exact h

-- ============================================================================
-- Sorry 2: Intersection volume at angle (SORRY — copy dune's proof)
-- ============================================================================

lemma intersection_volume_at_angle
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 1000)
    (T U : Kakeya.DeltaTube δ)
    (θ : ℝ) (hθ1 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    (h_eff : effectiveAngle T U = θ) :
    MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
      ENNReal.ofReal (16 * δ ^ 3 / Real.sin θ) := by
  let α := angleBetween T U
  have h_cs : |inner ℝ T.direction U.direction| ≤ 1 := by
    have h := abs_real_inner_le_norm T.direction U.direction
    rw [T.direction_unit, U.direction_unit] at h
    <;> norm_num at h ⊢ <;> exact h
  have hα1 : -1 ≤ inner ℝ T.direction U.direction := by
    linarith [abs_le.mp h_cs]
  have hα2 : inner ℝ T.direction U.direction ≤ 1 := by
    linarith [abs_le.mp h_cs]
  have hcosα : Real.cos α = inner ℝ T.direction U.direction := by
    simpa [α, angleBetween, Kakeya.Assouad.angleBetween] using
      Real.cos_arccos hα1 hα2
  by_cases h_case : α ≤ Real.pi / 2
  · have hθ_eq : α = θ := by
      have h_le : α ≤ Real.pi - α := by linarith [Real.pi_pos]
      have h : effectiveAngle T U = α := by
        rw [effectiveAngle, min_eq_left h_le]
      rw [h] at h_eff; exact h_eff
    have hsin : 0 < Real.sin θ := by
      rw [←hθ_eq]
      have h1 : 0 < α := by linarith [hθ1]
      have h2 : α < Real.pi := by linarith [Real.pi_pos]
      exact Real.sin_pos_of_pos_of_lt_pi h1 h2
    have hcos : inner ℝ T.direction U.direction = Real.cos θ := by
      rw [←hcosα, hθ_eq]
    exact Kakeya.Assouad.tube_intersection_volume_angle hδ hδ1 T U U.direction
      (Or.inl rfl) θ hθ1.le hθ2 hcos hsin
  · have hα_gt : α > Real.pi / 2 := by linarith
    have hα_le : α ≤ Real.pi := Real.arccos_le_pi _
    have hθ_eq : Real.pi - α = θ := by
      have h_le : Real.pi - α ≤ α := by linarith [Real.pi_pos]
      have h : effectiveAngle T U = Real.pi - α := by
        rw [effectiveAngle, min_eq_right h_le]
      rw [h] at h_eff; exact h_eff
    have hsin : 0 < Real.sin θ := by
      rw [←hθ_eq]
      have hpos : 0 < Real.pi - α := by linarith [Real.pi_pos]
      have hlt : Real.pi - α < Real.pi := by linarith [Real.pi_pos]
      exact Real.sin_pos_of_pos_of_lt_pi hpos hlt
    have hcos : inner ℝ T.direction (-U.direction) = Real.cos θ := by
      have h3 : Real.cos α = inner ℝ T.direction U.direction := hcosα
      have h4 : α = Real.pi - θ := by linarith
      have h5 : Real.cos α = -Real.cos θ := by
        rw [h4, Real.cos_pi_sub] <;> ring
      have h6 : inner ℝ T.direction (-U.direction) = -inner ℝ T.direction U.direction := by
        simp [inner_smul_right] <;> ring
      rw [h6, ←h3, h5] <;> ring
    exact Kakeya.Assouad.tube_intersection_volume_angle hδ hδ1 T U (-U.direction)
      (Or.inr rfl) θ hθ1.le hθ2 hcos hsin

-- ============================================================================
-- Geometric packing lemma
-- ============================================================================

/-- Volume of a set bounded by product of coordinate diameters under a linear isometry. -/
lemma volume_diameter_bound {E : Set Point3} (hE : MeasurableSet E)
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

/-- Perpendicular component of u relative to v has norm ≤ 2σ when effectiveAngle ≤ 2σ. -/
lemma perp_component_bound {δ : ℝ} (T U : Kakeya.DeltaTube δ)
    (σ : ℝ) (hσ : effectiveAngle T U ≤ 2 * σ) (h2σ : 2 * σ ≤ Real.pi / 2) :
    ‖U.direction - inner ℝ T.direction U.direction • T.direction‖ ≤ 2 * σ := by
  let v := T.direction
  let u := U.direction
  have hv : ‖v‖ = 1 := T.direction_unit
  have hu : ‖u‖ = 1 := U.direction_unit
  let c : ℝ := inner ℝ v u
  let α := angleBetween T U
  have hα1 : -1 ≤ c := by
    have h := abs_real_inner_le_norm v u
    rw [hv, hu] at h <;> norm_num at h ⊢ <;> linarith [abs_le.mp h]
  have hα2 : c ≤ 1 := by
    have h := abs_real_inner_le_norm v u
    rw [hv, hu] at h <;> norm_num at h ⊢ <;> linarith [abs_le.mp h]
  have hcos : Real.cos α = c := by
    simpa [α, angleBetween, Kakeya.Assouad.angleBetween] using
      Real.cos_arccos hα1 hα2
  have hvv : inner ℝ v v = 1 := by
    have h : inner ℝ v v = ‖v‖ ^ 2 := by
      exact real_inner_self_eq_norm_sq v
    rw [h, hv] <;> norm_num
  have h_orth : inner ℝ (c • v) (u - c • v) = 0 := by
    calc
      inner ℝ (c • v) (u - c • v)
        = c * inner ℝ v (u - c • v) := by simp [inner_smul_left] <;> ring
      _ = c * (inner ℝ v u - inner ℝ v (c • v)) := by rw [inner_sub_right] <;> ring
      _ = c * (inner ℝ v u - c * inner ℝ v v) := by rw [inner_smul_right] <;> ring
      _ = c * (c - c * 1) := by
        have h_vu : inner ℝ v u = c := by rfl
        rw [h_vu, hvv] <;> ring
      _ = 0 := by ring
  have h_pyth : ‖(c • v) + (u - c • v)‖ ^ 2 = ‖c • v‖ ^ 2 + ‖u - c • v‖ ^ 2 := by
    have h4 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • v) (u - c • v) h_orth
    simpa [pow_two] using h4
  have h_sum : (c • v) + (u - c • v) = u := by
    simp [c] <;> abel
  have h_norm_cv : ‖c • v‖ ^ 2 = c ^ 2 := by
    simp [norm_smul, hv] <;> ring
  have h_perp2 : ‖u - c • v‖ ^ 2 = 1 - c ^ 2 := by
    rw [h_sum] at h_pyth
    rw [h_norm_cv] at h_pyth
    rw [hu] at h_pyth
    linarith
  have h_sin2 : Real.sin α ^ 2 = 1 - c ^ 2 := by
    rw [←hcos]
    have h : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
    linarith
  have hα_nonneg : 0 ≤ α := Real.arccos_nonneg _
  have hα_le_pi : α ≤ Real.pi := Real.arccos_le_pi _
  have h_sin_nonneg : 0 ≤ Real.sin α := Real.sin_nonneg_of_mem_Icc ⟨hα_nonneg, hα_le_pi⟩
  have h_perp_nonneg : 0 ≤ ‖u - c • v‖ := by positivity
  have h_perp_eq : ‖u - c • v‖ = Real.sin α := by
    nlinarith [h_perp2, h_sin2]
  have h_eff_sin : Real.sin α = Real.sin (effectiveAngle T U) := by
    dsimp only [effectiveAngle]
    by_cases h : α ≤ Real.pi - α
    · rw [min_eq_left h]
    · rw [min_eq_right (by linarith), Real.sin_pi_sub]
  have h_goal : ‖u - c • v‖ ≤ 2 * σ := by
    rw [h_perp_eq, h_eff_sin]
    have h5 : Real.sin (effectiveAngle T U) ≤ effectiveAngle T U := Real.sin_le (effectiveAngle_nonneg T U)
    have h6 : effectiveAngle T U ≤ 2 * σ := hσ
    linarith
  simpa [c, v, u] using h_goal

/--
Helper for `direction_band_geometric`: the `e2`-coordinate bound in the
case `w ≠ 0`.  Extracted to keep the ONB construction small enough for
the elaborator.
-/
lemma direction_band_e2_bound
    {δ : ℝ} (hδ : 0 < δ)
    (v n w : Point3) (hv : ‖v‖ = 1)
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (a : ℝ) (ha_bound : |a| ≤ C0 * δ)
    (hwnorm2 : ‖w‖ ^ 2 = 1 - a ^ 2)
    (h_w : w ≠ 0)
    (e2 : Point3) (he2_unit : ‖e2‖ = 1)
    (hwe2 : w = ‖w‖ • e2)
    (hn_decomp : n = a • v + w) :
    ∀ (u : Point3), ‖u‖ = 1 → |inner ℝ u n| ≤ C0 * δ → |inner ℝ u e2| ≤ 4 * C0 * δ := by
  intro u hu hplane_u
  have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr h_w
  by_cases h_case : ‖w‖ ≥ 1 / 2
  · have h1 : inner ℝ u n = a * inner ℝ u v + ‖w‖ * inner ℝ u e2 := by
      rw [hn_decomp]
      have h3 : inner ℝ u (a • v + w) = a * inner ℝ u v + inner ℝ u w := by
        simp [inner_add_right, inner_smul_right] <;> ring
      rw [h3]
      have h4 : inner ℝ u w = ‖w‖ * inner ℝ u e2 := by
        have h5 : inner ℝ u w = inner ℝ u (‖w‖ • e2) := by
          exact congr_arg (fun x : Point3 => inner ℝ u x) hwe2
        rw [h5]
        exact inner_smul_right u e2 ‖w‖
      rw [h4] <;> ring
    have h3 : |‖w‖ * inner ℝ u e2| ≤ 2 * C0 * δ := by
      have h_eq : ‖w‖ * inner ℝ u e2 = inner ℝ u n - a * inner ℝ u v := by linarith [h1]
      rw [h_eq]
      have h4 : |inner ℝ u n| ≤ C0 * δ := hplane_u
      have h5 : |a * inner ℝ u v| ≤ C0 * δ := by
        have h6 : |inner ℝ u v| ≤ 1 := by
          have h7 := abs_real_inner_le_norm u v
          rw [hu, hv] at h7 <;> norm_num at h7 ⊢ <;> exact h7
        calc |a * inner ℝ u v| = |a| * |inner ℝ u v| := by rw [abs_mul]
          _ ≤ |a| * 1 := by gcongr
          _ = |a| := by ring
          _ ≤ C0 * δ := ha_bound
      have h_tri : |inner ℝ u n - a * inner ℝ u v| ≤ |inner ℝ u n| + |a * inner ℝ u v| :=
        abs_sub (inner ℝ u n) (a * inner ℝ u v)
      calc |inner ℝ u n - a * inner ℝ u v|
        ≤ |inner ℝ u n| + |a * inner ℝ u v| := h_tri
      _ ≤ C0 * δ + C0 * δ := by gcongr
      _ = 2 * C0 * δ := by ring
    have h4 : ‖w‖ * |inner ℝ u e2| ≤ 2 * C0 * δ := by
      have h5 : |‖w‖ * inner ℝ u e2| = ‖w‖ * |inner ℝ u e2| := by
        rw [abs_mul] <;> rw [abs_of_nonneg (norm_nonneg w)]
      rw [h5] at h3; exact h3
    have h6 : |inner ℝ u e2| ≤ 2 * C0 * δ / ‖w‖ := by
      calc |inner ℝ u e2|
        = (‖w‖ * |inner ℝ u e2|) / ‖w‖ := by field_simp [hwnorm_pos.ne'] <;> ring
      _ ≤ (2 * C0 * δ) / ‖w‖ := by gcongr
    calc |inner ℝ u e2| ≤ 2 * C0 * δ / ‖w‖ := h6
      _ ≤ 2 * C0 * δ / (1 / 2) := by gcongr
      _ = 4 * C0 * δ := by ring
  · have h_lt : ‖w‖ < 1 / 2 := by linarith
    have h_a2 : a ^ 2 > 3 / 4 := by
      have h1 : ‖w‖ ^ 2 < 1 / 4 := by
        have h2 : 0 ≤ ‖w‖ := norm_nonneg w
        nlinarith
      linarith [hwnorm2]
    have h_abs : |a| > 1 / 2 := by
      have h7 : a ^ 2 > 3 / 4 := h_a2
      by_cases h8 : 0 ≤ a
      · have h9 : a > 1 / 2 := by nlinarith
        rw [abs_of_nonneg h8] <;> linarith
      · have h9 : a < -1 / 2 := by nlinarith
        rw [abs_of_neg (by linarith)] <;> linarith
    have hC0δ : 1 / 2 < C0 * δ := by linarith [ha_bound]
    have h1 : |inner ℝ u e2| ≤ 1 := by
      have h2 := abs_real_inner_le_norm u e2
      rw [hu, he2_unit] at h2 <;> norm_num at h2 ⊢ <;> exact h2
    have h3 : 1 ≤ 4 * C0 * δ := by linarith
    linarith

/--
Construct an orthonormal basis (v, e2, e3) and a linear isometry A mapping
(v, e2, e3) to the standard basis.  e2 is aligned with the projection of n
onto v⊥ when possible.  Also provides the bound |inner u e2| ≤ 4C₀δ for
unit vectors u with |inner u n| ≤ C₀δ.
-/
lemma direction_band_onb
    {δ : ℝ} (hδ : 0 < δ)
    (v n : Point3) (hv : ‖v‖ = 1) (hn : ‖n‖ = 1)
    (C0 : ℝ) (hC0 : 0 ≤ C0)
    (h_plane_v : |inner ℝ v n| ≤ C0 * δ) :
    ∃ (A : Point3 ≃ₗᵢ[ℝ] Point3) (e2 e3 : Point3),
      A v = EuclideanSpace.single (0 : Fin 3) 1 ∧
      A e2 = EuclideanSpace.single (1 : Fin 3) 1 ∧
      A e3 = EuclideanSpace.single (2 : Fin 3) 1 ∧
      ‖e2‖ = 1 ∧ ‖e3‖ = 1 ∧
      inner ℝ v e2 = 0 ∧ inner ℝ v e3 = 0 ∧ inner ℝ e2 e3 = 0 ∧
      (∀ (u : Point3), ‖u‖ = 1 → |inner ℝ u n| ≤ C0 * δ → |inner ℝ u e2| ≤ 4 * C0 * δ) := by
  let a : ℝ := inner ℝ n v
  let w : Point3 := n - a • v
  have hw_perp : inner ℝ w v = 0 := by
    dsimp only [w]
    have h1 : inner ℝ (n - a • v) v =
        inner ℝ n v - inner ℝ (a • v) v := by
      exact inner_sub_left n (a • v) v
    rw [h1]
    have h2 : inner ℝ (a • v) v = a * inner ℝ v v := by
      simp [inner_smul_left] <;> ring
    rw [h2]
    have h3 : inner ℝ v v = 1 := by
      have h4 : inner ℝ v v = ‖v‖ ^ 2 := by
        exact real_inner_self_eq_norm_sq v
      rw [h4, hv] <;> norm_num
    rw [h3] <;> ring
  have hwnorm2 : ‖w‖ ^ 2 = 1 - a ^ 2 := by
    have h1 : n = a • v + w := by simp [w] <;> abel
    have h2 : inner ℝ (a • v) w = 0 := by
      have h21 : inner ℝ (a • v) w = a * inner ℝ v w := by
        simp [inner_smul_left] <;> ring
      rw [h21]
      have h_comm : inner ℝ v w = inner ℝ w v := (real_inner_comm v w).symm
      rw [h_comm]
      rw [hw_perp] <;> ring
    have h3 : ‖n‖ ^ 2 = ‖a • v + w‖ ^ 2 := by rw [h1]
    have h4_raw := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • v) w h2
    have h4 : ‖a • v + w‖ ^ 2 = ‖a • v‖ ^ 2 + ‖w‖ ^ 2 := by
      simpa [pow_two] using h4_raw
    have h5 : ‖a • v‖ ^ 2 = a ^ 2 := by
      simp [norm_smul, hv] <;> ring
    have h6 : ‖n‖ ^ 2 = 1 := by rw [hn] <;> norm_num
    linarith
  have ha_bound : |a| ≤ C0 * δ := by
    have h1 : a = inner ℝ v n := by
      dsimp only [a]
      rw [real_inner_comm n v]
    rw [h1]
    exact h_plane_v
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1_std : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2_std : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have he0_norm : ‖e0_std‖ = 1 := by simp [e0_std] <;> norm_num
  have he1_norm : ‖e1_std‖ = 1 := by simp [e1_std] <;> norm_num
  have he2_norm : ‖e2_std‖ = 1 := by simp [e2_std] <;> norm_num
  let A0 : Point3 ≃ₗᵢ[ℝ] Point3 := Submodule.reflection (ℝ ∙ (v - e0_std))ᗮ
  have hA0_v : A0 v = e0_std := Submodule.reflection_sub (by rw [hv, he0_norm])

  by_cases h_w : w = 0
  · -- Case w = 0: C0*δ ≥ 1, any e2 works
    have ha2 : a ^ 2 = 1 := by
      rw [h_w] at hwnorm2
      have h0 : ‖(0 : Point3)‖ ^ 2 = 0 := by simp
      rw [h0] at hwnorm2
      linarith
    have h_abs : |a| = 1 := by
      have h2 : |a| ^ 2 = 1 := by
        rw [sq_abs] <;> exact ha2
      have h3 : 0 ≤ |a| := abs_nonneg a
      nlinarith
    have hC0δ : 1 ≤ C0 * δ := by linarith [ha_bound, h_abs]
    let e2 := A0.symm e1_std
    let e3 := A0.symm e2_std
    have hA0_e2 : A0 e2 = e1_std := by simp [e2]
    have hA0_e3 : A0 e3 = e2_std := by simp [e3]
    have he2_unit : ‖e2‖ = 1 := by
      have h : ‖e2‖ = ‖e1_std‖ := A0.symm.norm_map e1_std
      rw [h, he1_norm]
    have he3_unit : ‖e3‖ = 1 := by
      have h : ‖e3‖ = ‖e2_std‖ := A0.symm.norm_map e2_std
      rw [h, he2_norm]
    have hv_e2 : inner ℝ v e2 = 0 := by
      have h : inner ℝ v e2 = inner ℝ (A0 v) (A0 e2) := (A0.inner_map_map v e2).symm
      rw [h, hA0_v, hA0_e2]
      simp [e0_std, e1_std, EuclideanSpace.inner_single_right] <;> norm_num
    have hv_e3 : inner ℝ v e3 = 0 := by
      have h : inner ℝ v e3 = inner ℝ (A0 v) (A0 e3) := (A0.inner_map_map v e3).symm
      rw [h, hA0_v, hA0_e3]
      simp [e0_std, e2_std, EuclideanSpace.inner_single_right] <;> norm_num
    have he2_e3 : inner ℝ e2 e3 = 0 := by
      have h : inner ℝ e2 e3 = inner ℝ (A0 e2) (A0 e3) := (A0.inner_map_map e2 e3).symm
      rw [h, hA0_e2, hA0_e3]
      simp [e1_std, e2_std, EuclideanSpace.inner_single_right] <;> norm_num
    have h_e2_bound : ∀ (u : Point3), ‖u‖ = 1 → |inner ℝ u n| ≤ C0 * δ → |inner ℝ u e2| ≤ 4 * C0 * δ := by
      intro u hu _
      have h1 : |inner ℝ u e2| ≤ 1 := by
        have h2 := abs_real_inner_le_norm u e2
        rw [hu, he2_unit] at h2 <;> norm_num at h2 ⊢ <;> exact h2
      have h3 : 1 ≤ 4 * C0 * δ := by linarith
      linarith
    exact ⟨A0, e2, e3, hA0_v, hA0_e2, hA0_e3, he2_unit, he3_unit, hv_e2, hv_e3, he2_e3, h_e2_bound⟩
  · -- Case w ≠ 0: align e2 with w/‖w‖
    have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr h_w
    let e2 : Point3 := (‖w‖)⁻¹ • w
    have he2_unit : ‖e2‖ = 1 := by
      simp [e2, norm_smul, hwnorm_pos.ne'] <;> field_simp [hwnorm_pos.ne'] <;> ring
    have he2_perp : inner ℝ v e2 = 0 := by
      have h1 : inner ℝ v e2 = (‖w‖)⁻¹ * inner ℝ v w := by
        simp [e2, inner_smul_right] <;> ring
      rw [h1]
      have h2 : inner ℝ v w = inner ℝ w v := (real_inner_comm v w).symm
      rw [h2, hw_perp] <;> ring
    let w' : Point3 := A0 w
    have hw'_norm : ‖w'‖ = ‖w‖ := A0.norm_map w
    have hw'_e0 : inner ℝ w' e0_std = 0 := by
      have h : inner ℝ w' e0_std = inner ℝ w (A0.symm e0_std) := by
        have h4 := A0.inner_map_map w (A0.symm e0_std)
        have h5 : A0 (A0.symm e0_std) = e0_std := A0.apply_symm_apply e0_std
        rw [h5] at h4; exact h4
      rw [h]
      have h6 : A0.symm e0_std = v := by
        have h7 : A0 (A0.symm e0_std) = A0 v := by rw [A0.apply_symm_apply, hA0_v]
        exact A0.injective h7
      rw [h6, hw_perp]
    let u_std : Point3 := (‖w'‖)⁻¹ • w'
    have hu_std_unit : ‖u_std‖ = 1 := by
      simp [u_std, norm_smul, hw'_norm, hwnorm_pos.ne'] <;> field_simp <;> ring
    have hu_std_e0 : inner ℝ u_std e0_std = 0 := by
      simp [u_std, inner_smul_left, hw'_e0] <;> ring
    let R : Point3 ≃ₗᵢ[ℝ] Point3 := Submodule.reflection (ℝ ∙ (u_std - e1_std))ᗮ
    have hR_u : R u_std = e1_std := Submodule.reflection_sub (by rw [hu_std_unit, he1_norm])
    have hR_e0 : R e0_std = e0_std := by
      have h_orth : inner ℝ e0_std (u_std - e1_std) = 0 := by
        have h1 : inner ℝ e0_std u_std = 0 := by
          have h_comm : inner ℝ e0_std u_std = inner ℝ u_std e0_std := (real_inner_comm e0_std u_std).symm
          rw [h_comm, hu_std_e0] <;> ring
        have h2 : inner ℝ e0_std e1_std = 0 := by
          simp [e0_std, e1_std, EuclideanSpace.inner_single_right] <;> norm_num
        have h3 : inner ℝ e0_std (u_std - e1_std) = inner ℝ e0_std u_std - inner ℝ e0_std e1_std := by
          rw [inner_sub_right] <;> ring
        rw [h3, h1, h2] <;> ring
      have h_in : e0_std ∈ (ℝ ∙ (u_std - e1_std))ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro z hz
        rcases (Submodule.mem_span_singleton).mp hz with ⟨c, rfl⟩
        simp [inner_smul_right, h_orth] <;> ring
      exact Submodule.reflection_mem_subspace_eq_self h_in
    let A : Point3 ≃ₗᵢ[ℝ] Point3 := A0.trans R
    let e3 : Point3 := A.symm e2_std
    have hA_v : A v = e0_std := by
      simp [A, hA0_v, hR_e0]
    have hA_e2 : A e2 = e1_std := by
      have h1 : A0 e2 = u_std := by
        have h2 : A0 e2 = (‖w‖)⁻¹ • A0 w := by
          simp [e2, map_smul] <;> ring
        rw [h2]
        have h3 : (‖w‖)⁻¹ • A0 w = (‖w'‖)⁻¹ • w' := by rw [hw'_norm] <;> rfl
        rw [h3] <;> rfl
      simp [A, h1, hR_u]
    have hA_e3 : A e3 = e2_std := by simp [e3]
    have he3_unit : ‖e3‖ = 1 := by
      have h : ‖e3‖ = ‖e2_std‖ := A.symm.norm_map e2_std
      rw [h, he2_norm]
    have hv_e3 : inner ℝ v e3 = 0 := by
      have h : inner ℝ v e3 = inner ℝ (A v) (A e3) := (A.inner_map_map v e3).symm
      rw [h, hA_v, hA_e3]
      simp [e0_std, e2_std, EuclideanSpace.inner_single_right] <;> norm_num
    have he2_e3 : inner ℝ e2 e3 = 0 := by
      have h : inner ℝ e2 e3 = inner ℝ (A e2) (A e3) := (A.inner_map_map e2 e3).symm
      rw [h, hA_e2, hA_e3]
      simp [e1_std, e2_std, EuclideanSpace.inner_single_right] <;> norm_num
    have hwe2 : w = ‖w‖ • e2 := by
      have h6 : ‖w‖ ≠ 0 := hwnorm_pos.ne'
      have h7 : ‖w‖ • e2 = w := by
        dsimp only [e2]
        have h9 : ‖w‖ • ((‖w‖)⁻¹ • w) = (‖w‖ * (‖w‖)⁻¹) • w := by
          exact smul_smul ‖w‖ ‖w‖⁻¹ w
        rw [h9]
        have h10 : ‖w‖ * (‖w‖)⁻¹ = 1 := by field_simp [h6]
        rw [h10, one_smul]
      exact h7.symm
    have hn_decomp : n = a • v + w := by simp [w] <;> abel
    have h_e2_bound : ∀ (u : Point3), ‖u‖ = 1 → |inner ℝ u n| ≤ C0 * δ → |inner ℝ u e2| ≤ 4 * C0 * δ :=
      direction_band_e2_bound hδ v n w hv C0 hC0 a ha_bound hwnorm2 h_w e2 he2_unit hwe2 hn_decomp
    exact ⟨A, e2, e3, hA_v, hA_e2, hA_e3, he2_unit, he3_unit, he2_perp, hv_e3, he2_e3, h_e2_bound⟩

end Kakeya.Hairbrush
