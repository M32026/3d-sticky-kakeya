import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Geometry
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi


open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace Kakeya.CV

noncomputable section

/-- Volume of a cone with height `a > 0` and base radius `R ≥ 0`, apex at origin,
axis along coordinate 0. -/
lemma cone_volume_exact (a R : ℝ) (ha : 0 < a) (hR : 0 ≤ R) :
    volume {p : Point 3 | 0 ≤ p 0 ∧ p 0 ≤ a ∧ (p 1)^2 + (p 2)^2 ≤ (p 0 / a)^2 * R^2}
    = ENNReal.ofReal (Real.pi * R^2 * a / 3) := by
  let e1 : Point 3 ≃ (Fin 3 → ℝ) := WithLp.equiv 2 (Fin 3 → ℝ)
  have h1_mp : MeasurePreserving e1 volume volume := PiLp.volume_preserving_ofLp (ι := Fin 3)
  let S_pi : Set (Fin 3 → ℝ) := {f | 0 ≤ f 0 ∧ f 0 ≤ a ∧ (f 1)^2 + (f 2)^2 ≤ (f 0 / a)^2 * R^2}
  have hS_pi_meas : MeasurableSet S_pi := by
    have h1 : MeasurableSet {f : Fin 3 → ℝ | 0 ≤ f 0} := measurableSet_le (by fun_prop) (by fun_prop)
    have h2 : MeasurableSet {f : Fin 3 → ℝ | f 0 ≤ a} := measurableSet_le (by fun_prop) (by fun_prop)
    have h3 : MeasurableSet {f : Fin 3 → ℝ | (f 1)^2 + (f 2)^2 ≤ (f 0 / a)^2 * R^2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter h3)
  have hS_preimage : e1 ⁻¹' S_pi = {p : Point 3 | 0 ≤ p 0 ∧ p 0 ≤ a ∧ (p 1)^2 + (p 2)^2 ≤ (p 0 / a)^2 * R^2} := by
    ext p; simp [S_pi, e1, WithLp.equiv] <;> rfl
  have h_vol1 : volume (e1 ⁻¹' S_pi) = volume S_pi := h1_mp.measure_preimage hS_pi_meas.nullMeasurableSet
  let e2 : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h2_mp : MeasurePreserving e2 volume volume := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let S_prod : Set (ℝ × (Fin 2 → ℝ)) := e2 '' S_pi
  have hS_prod_meas : MeasurableSet S_prod := e2.measurableSet_image.mpr hS_pi_meas
  have hS_prod_eq : S_prod = {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1 ∧ p.1 ≤ a ∧ (p.2 0)^2 + (p.2 1)^2 ≤ (p.1 / a)^2 * R^2} := by
    ext ⟨x, q⟩
    simp only [S_prod, Set.mem_image, Set.mem_setOf_eq, S_pi]
    constructor
    · rintro ⟨f, hf, h_eq⟩
      have hx : x = f 0 := by
        have h : (e2 f).1 = f 0 := by rfl
        rw [h_eq] at h; exact h
      have hq0 : q 0 = f 1 := by
        have h : (e2 f).2 0 = f 1 := by rfl
        rw [h_eq] at h; exact h
      have hq1 : q 1 = f 2 := by
        have h : (e2 f).2 1 = f 2 := by rfl
        rw [h_eq] at h; exact h
      rw [hx, hq0, hq1]; exact hf
    · rintro ⟨h1', h2', h3'⟩
      let f : Fin 3 → ℝ := e2.symm (x, q)
      have hfe : e2 f = (x, q) := e2.apply_symm_apply (x, q)
      have hf0 : f 0 = x := by
        have h : (e2 f).1 = f 0 := by rfl
        have h2 : (e2 f).1 = x := by rw [hfe] <;> rfl
        exact h.symm.trans h2
      have hf1 : f 1 = q 0 := by
        have h : (e2 f).2 0 = f 1 := by rfl
        have h2 : (e2 f).2 0 = q 0 := by rw [hfe] <;> rfl
        exact h.symm.trans h2
      have hf2 : f 2 = q 1 := by
        have h : (e2 f).2 1 = f 2 := by rfl
        have h2 : (e2 f).2 1 = q 1 := by rw [hfe] <;> rfl
        exact h.symm.trans h2
      have h_ineq : (f 1)^2 + (f 2)^2 ≤ (f 0 / a)^2 * R^2 := by
        rw [hf1, hf2, hf0]; exact h3'
      exact ⟨f, ⟨by linarith, by linarith, h_ineq⟩, hfe⟩
  have h_preimg : e2 ⁻¹' S_prod = S_pi := by ext z; simp [S_prod]
  have h_vol2 : volume S_pi = volume S_prod := by
    have h : volume (e2 ⁻¹' S_prod) = volume S_prod := h2_mp.measure_preimage hS_prod_meas.nullMeasurableSet
    rw [h_preimg] at h; exact h
  rw [← hS_preimage, h_vol1, h_vol2, hS_prod_eq]
  -- Disk volume helper
  have h_disk_vol : ∀ (r : ℝ), 0 ≤ r → volume {q : Fin 2 → ℝ | (q 0)^2 + (q 1)^2 ≤ r^2} = ENNReal.ofReal (Real.pi * r^2) := by
    intro r hr
    let e3 : Point 2 ≃ (Fin 2 → ℝ) := WithLp.equiv 2 (Fin 2 → ℝ)
    have h3_mp : MeasurePreserving e3 volume volume := PiLp.volume_preserving_ofLp (ι := Fin 2)
    have h_set_meas : MeasurableSet {q : Fin 2 → ℝ | (q 0)^2 + (q 1)^2 ≤ r^2} := by
      have h1 : Measurable (fun (q : Fin 2 → ℝ) => (q 0)^2 + (q 1)^2) := by fun_prop
      have h2 : Measurable (fun (q : Fin 2 → ℝ) => r^2) := by fun_prop
      exact measurableSet_le h1 h2
    have h4 : e3 ⁻¹' {q : Fin 2 → ℝ | (q 0)^2 + (q 1)^2 ≤ r^2} = closedBall (0 : Point 2) r := by
      ext p
      have h5 : (e3 p 0)^2 + (e3 p 1)^2 = ‖p‖^2 := by
        simp [e3, WithLp.equiv, norm_sq_point2] <;> ring
      simp only [Set.mem_preimage, Set.mem_setOf_eq, closedBall, dist_zero_right]
      rw [h5]
      have h6 : 0 ≤ ‖p‖ := by positivity
      constructor <;> intro h7 <;> nlinarith
    have h5 : volume (e3 ⁻¹' {q : Fin 2 → ℝ | (q 0)^2 + (q 1)^2 ≤ r^2}) = volume {q : Fin 2 → ℝ | (q 0)^2 + (q 1)^2 ≤ r^2} :=
      h3_mp.measure_preimage h_set_meas.nullMeasurableSet
    rw [h4] at h5
    rw [← h5, EuclideanSpace.volume_closedBall (Fin 2) 0 r]
    have h_gamma : Real.Gamma (1 + 1) = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 1
    have h_sqrt_pi_sq : (Real.sqrt Real.pi)^2 = Real.pi := Real.sq_sqrt (by positivity)
    have h_formula : (Real.sqrt Real.pi)^2 / Real.Gamma (1 + 1) = Real.pi := by
      rw [h_gamma, h_sqrt_pi_sq] <;> ring
    have h_goal : ENNReal.ofReal r ^ 2 * ENNReal.ofReal ((Real.sqrt Real.pi)^2 / Real.Gamma (1 + 1)) = ENNReal.ofReal (Real.pi * r^2) := by
      have h_formula2 : ENNReal.ofReal ((Real.sqrt Real.pi)^2 / Real.Gamma (1 + 1)) = ENNReal.ofReal Real.pi := by rw [h_formula]
      rw [h_formula2]
      have h1 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r^2) := by rw [← ENNReal.ofReal_pow hr] <;> rfl
      rw [h1, ← ENNReal.ofReal_mul (by positivity)] <;> congr 1 <;> ring
    have h_card : Fintype.card (Fin 2) = 2 := by simp
    simpa [h_card, h_formula] using h_goal
  let S' : Set (ℝ × (Fin 2 → ℝ)) := {p | 0 ≤ p.1 ∧ p.1 ≤ a ∧ (p.2 0)^2 + (p.2 1)^2 ≤ (p.1 / a)^2 * R^2}
  have hS'_meas : MeasurableSet S' := by
    have h1 : MeasurableSet {p : ℝ × (Fin 2 → ℝ) | 0 ≤ p.1} := measurableSet_Ici.preimage measurable_fst
    have h2 : MeasurableSet {p : ℝ × (Fin 2 → ℝ) | p.1 ≤ a} := measurableSet_Iic.preimage measurable_fst
    have h3 : MeasurableSet {p : ℝ × (Fin 2 → ℝ) | (p.2 0)^2 + (p.2 1)^2 ≤ (p.1 / a)^2 * R^2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    exact h1.inter (h2.inter h3)
  have h_fub : (volume.prod volume) S' = ∫⁻ (x : ℝ), volume {q : Fin 2 → ℝ | (x, q) ∈ S'} ∂volume := by
    rw [Measure.prod_apply hS'_meas] <;> rfl
  have h_inner_set : ∀ (x : ℝ), {q : Fin 2 → ℝ | (x, q) ∈ S'} = {q | 0 ≤ x ∧ x ≤ a ∧ (q 0)^2 + (q 1)^2 ≤ (x / a)^2 * R^2} := by
    intro x; ext q; simp [S'] <;> tauto
  rw [MeasureTheory.Measure.volume_eq_prod ℝ (Fin 2 → ℝ)]
  rw [h_fub]
  let f : ℝ → ENNReal := fun x => if 0 ≤ x ∧ x ≤ a then ENNReal.ofReal (Real.pi * (x / a * R)^2) else 0
  have h_inner_eq : ∀ (x : ℝ), volume {q : Fin 2 → ℝ | (x, q) ∈ S'} = f x := by
    intro x
    simp only [f]
    rw [h_inner_set x]
    by_cases h : 0 ≤ x ∧ x ≤ a
    · rw [if_pos h]
      have h_eq : (x / a)^2 * R^2 = (x / a * R)^2 := by ring
      have h_set_eq : {q : Fin 2 → ℝ | 0 ≤ x ∧ x ≤ a ∧ (q 0)^2 + (q 1)^2 ≤ (x / a)^2 * R^2} =
          {q : Fin 2 → ℝ | (q 0)^2 + (q 1)^2 ≤ (x / a * R)^2} := by
        ext q
        simp only [Set.mem_setOf_eq]
        constructor
        · intro hq
          have h_ineq : (q 0)^2 + (q 1)^2 ≤ (x / a)^2 * R^2 := hq.2.2
          have h_goal : (q 0)^2 + (q 1)^2 ≤ (x / a * R)^2 := by
            rw [←h_eq]; exact h_ineq
          exact h_goal
        · intro hq
          have hq' : (q 0)^2 + (q 1)^2 ≤ (x / a)^2 * R^2 := by
            have h_ineq : (q 0)^2 + (q 1)^2 ≤ (x / a * R)^2 := hq
            have h_goal : (x / a * R)^2 = (x / a)^2 * R^2 := by ring
            rw [h_goal] at h_ineq; exact h_ineq
          exact ⟨h.1, h.2, hq'⟩
      rw [h_set_eq]
      have hr' : 0 ≤ x / a * R := by
        have hx : 0 ≤ x := h.1
        exact mul_nonneg (div_nonneg hx (by linarith)) hR
      exact h_disk_vol (x / a * R) hr'
    · rw [if_neg h]
      have h_set_empty : {q : Fin 2 → ℝ | 0 ≤ x ∧ x ≤ a ∧ (q 0)^2 + (q 1)^2 ≤ (x / a)^2 * R^2} = (∅ : Set (Fin 2 → ℝ)) := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h_cont
        exact h ⟨h_cont.1, h_cont.2.1⟩
      rw [h_set_empty]; simp
  rw [lintegral_congr h_inner_eq]
  -- Integral computation
  let g : ℝ → ℝ := fun x => if 0 < x ∧ x ≤ a then Real.pi * (x / a * R)^2 else 0
  have hg_nonneg : ∀ x, 0 ≤ g x := by intro x; by_cases h : 0 < x ∧ x ≤ a <;> simp [g, h] <;> positivity
  have h1_g : g = Set.indicator (Set.Ioc (0 : ℝ) a) (fun x : ℝ => Real.pi * (x / a * R)^2) := by
    funext x; by_cases h : x ∈ Set.Ioc (0 : ℝ) a
    · have h' : 0 < x ∧ x ≤ a := by simpa [Set.mem_Ioc] using h
      simp [g, h, h']
    · have h' : ¬(0 < x ∧ x ≤ a) := by simpa [Set.mem_Ioc] using h
      simp [g, h, h']
  have h_cont : Continuous (fun x : ℝ => Real.pi * (x / a * R)^2) := by fun_prop
  have h_on : IntegrableOn (fun x : ℝ => Real.pi * (x / a * R)^2) (Set.Ioc (0 : ℝ) a) volume :=
    h_cont.integrableOn_Ioc
  have hg_int : Integrable g volume := by
    rw [h1_g, integrable_indicator_iff measurableSet_Ioc]
    exact h_on
  have h_integral : ∫ x, g x ∂volume = Real.pi * R^2 * a / 3 := by
    rw [h1_g, integral_indicator measurableSet_Ioc]
    have h3 : ∫ (x : ℝ) in Set.Ioc (0 : ℝ) a, Real.pi * (x / a * R)^2 ∂volume =
        ∫ (x : ℝ) in (0 : ℝ)..a, Real.pi * (x / a * R)^2 := by
      exact (intervalIntegral.integral_of_le (by linarith)).symm
    rw [h3]
    have h5 : ∫ (x : ℝ) in (0)..a, Real.pi * (x / a * R)^2 = Real.pi * R^2 * a / 3 := by
      have h6 : ∫ (x : ℝ) in (0)..a, x^2 = a^3 / 3 := by rw [integral_pow] <;> ring
      have h_eq : ∀ (x : ℝ), Real.pi * (x / a * R)^2 = (Real.pi * R^2 / a^2) * x^2 := by intro x; ring
      have h_int_eq : ∫ (x : ℝ) in (0)..a, Real.pi * (x / a * R)^2 =
          ∫ (x : ℝ) in (0)..a, (Real.pi * R^2 / a^2) * x^2 := by
        apply intervalIntegral.integral_congr
        intro x _
        exact h_eq x
      rw [h_int_eq, intervalIntegral.integral_const_mul, h6]
      field_simp [ha.ne'] <;> ring
    exact h5
  have h_inner2 : ∀ (x : ℝ), (if 0 ≤ x ∧ x ≤ a then ENNReal.ofReal (Real.pi * (x / a * R)^2) else 0) = ENNReal.ofReal (g x) := by
    intro x
    by_cases h : 0 ≤ x ∧ x ≤ a
    · rw [if_pos h]
      by_cases h0 : x = 0
      · have h1 : Real.pi * (x / a * R)^2 = 0 := by rw [h0] <;> ring
        have h2 : g x = 0 := by
          have h3 : ¬(0 < x ∧ x ≤ a) := by intro h4; rw [h0] at h4; linarith
          simp [g, h3]
        rw [h1, h2] <;> simp
      · have hpos : 0 < x := by by_contra h'; exact h0 (by linarith)
        have h' : 0 < x ∧ x ≤ a := ⟨hpos, h.2⟩
        have hg : g x = Real.pi * (x / a * R)^2 := by simp [g, h']
        rw [hg]
    · rw [if_neg h]
      have h' : ¬(0 < x ∧ x ≤ a) := by intro h''; exact h ⟨by linarith, h''.2⟩
      have hg : g x = 0 := by simp [g, h']
      rw [hg] <;> simp
  rw [lintegral_congr h_inner2]
  have h_eq1 : (∫⁻ x, ENNReal.ofReal (g x) ∂volume).toReal = ∫ x, g x ∂volume :=
    (integral_eq_lintegral_of_nonneg_ae (by filter_upwards with x; exact hg_nonneg x) hg_int.aestronglyMeasurable).symm
  have h_lt_top : (∫⁻ x, ENNReal.ofReal (g x) ∂volume) < ⊤ :=
    hg_int.lintegral_lt_top
  rw [← ENNReal.ofReal_toReal h_lt_top.ne, h_eq1, h_integral]

end

end Kakeya.CV
