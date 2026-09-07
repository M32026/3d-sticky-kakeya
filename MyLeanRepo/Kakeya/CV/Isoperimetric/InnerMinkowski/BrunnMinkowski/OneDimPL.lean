import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.OneDim
import Mathlib.MeasureTheory.Integral.Layercake

open scoped Pointwise

open MeasureTheory ENNReal Metric Set

namespace Geometry

/-!
# 1D Prékopa–Leindler Inequality (Clean version)

Proof via layer cake + 1D Brunn–Minkowski + optimized threshold scaling.
-/

/-! ### Helper lemmas -/

/-- Volume scaling in 1D. -/
lemma volume_smul_real {c : ℝ} (hc : 0 < c) {A : Set ℝ} (hA : MeasurableSet A) :
    volume (c • A) = ENNReal.ofReal c * volume A := by
  let f : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  have h1 : c • A = f '' A := by ext x; simp [Set.mem_smul_set] <;> rfl
  rw [h1, MeasureTheory.Measure.addHaar_image_continuousLinearMap volume f A]
  have hdet : LinearMap.det (f : ℝ →ₗ[ℝ] ℝ) = c := by simp [f]
  rw [hdet, abs_of_pos hc] <;> rfl

/-- Weighted AM-GM for ENNReal. -/
lemma ennreal_weighted_am_gm {u v : ENNReal} {t : ℝ}
    (ht1 : 0 < t) (ht2 : t < 1) :
    ENNReal.ofReal (1 - t) * u + ENNReal.ofReal t * v ≥ u ^ (1 - t) * v ^ t := by
  have h1pos : 0 < 1 - t := by linarith
  by_cases hu : u = ⊤
  · rw [hu]; have hpos : 0 < ENNReal.ofReal (1 - t) := by positivity
    have h : ENNReal.ofReal (1 - t) * (⊤ : ENNReal) = ⊤ := by
      rw [ENNReal.mul_top hpos.ne']
    rw [h]; simp
  · by_cases hv : v = ⊤
    · rw [hv]; have hpos : 0 < ENNReal.ofReal t := by positivity
      have h : ENNReal.ofReal t * (⊤ : ENNReal) = ⊤ := by
        rw [ENNReal.mul_top hpos.ne']
      rw [h]; simp
    · by_cases huz : u = 0
      · rw [huz]; have h : (0 : ENNReal) ^ (1 - t) = 0 := ENNReal.zero_rpow_of_pos h1pos
        rw [h]; simp
      · by_cases hvz : v = 0
        · rw [hvz]; have h : (0 : ENNReal) ^ t = 0 := ENNReal.zero_rpow_of_pos ht1
          rw [h]; simp
        · let x : ℝ := u.toReal; let y : ℝ := v.toReal
          have hx_pos : 0 < x := ENNReal.toReal_pos huz hu
          have hy_pos : 0 < y := ENNReal.toReal_pos hvz hv
          have h_real : x ^ (1 - t) * y ^ t ≤ (1 - t) * x + t * y :=
            Real.geom_mean_le_arith_mean2_weighted (by linarith) (by linarith) hx_pos.le hy_pos.le (by linarith)
          have h_ofReal_x : ENNReal.ofReal x = u := ENNReal.ofReal_toReal hu
          have h_ofReal_y : ENNReal.ofReal y = v := ENNReal.ofReal_toReal hv
          have h1a : (ENNReal.ofReal x) ^ (1 - t) = ENNReal.ofReal (x ^ (1 - t)) :=
            ENNReal.ofReal_rpow_of_nonneg hx_pos.le (by linarith)
          have h1 : ENNReal.ofReal (x ^ (1 - t)) = u ^ (1 - t) := by
            rw [←h1a, h_ofReal_x]
          have h2a : (ENNReal.ofReal y) ^ t = ENNReal.ofReal (y ^ t) :=
            ENNReal.ofReal_rpow_of_nonneg hy_pos.le (by linarith)
          have h2 : ENNReal.ofReal (y ^ t) = v ^ t := by
            rw [←h2a, h_ofReal_y]
          have h31 : 0 ≤ x ^ (1 - t) := by positivity
          have h32 : 0 ≤ y ^ t := by positivity
          have h3 : ENNReal.ofReal (x ^ (1 - t) * y ^ t) = u ^ (1 - t) * v ^ t := by
            have h_mul : ENNReal.ofReal (x ^ (1 - t) * y ^ t) =
                ENNReal.ofReal (x ^ (1 - t)) * ENNReal.ofReal (y ^ t) := by
              simp [h31, h32]
            rw [h_mul, h1, h2]
          have h4 : 0 ≤ (1 - t) * x := by positivity
          have h5 : 0 ≤ t * y := by positivity
          have h6 : ENNReal.ofReal ((1 - t) * x + t * y) =
              ENNReal.ofReal ((1 - t) * x) + ENNReal.ofReal (t * y) := by
            rw [ENNReal.ofReal_add h4 h5]
          have h7 : ENNReal.ofReal ((1 - t) * x) = ENNReal.ofReal (1 - t) * u := by
            rw [ENNReal.ofReal_mul, h_ofReal_x] <;> linarith
          have h8 : ENNReal.ofReal (t * y) = ENNReal.ofReal t * v := by
            rw [ENNReal.ofReal_mul, h_ofReal_y] <;> linarith
          have h9 : ENNReal.ofReal (x ^ (1 - t) * y ^ t) ≤ ENNReal.ofReal ((1 - t) * x + t * y) := by
            gcongr
          rw [h3, h6, h7, h8] at h9
          exact h9

/-- ENNReal identity: `x^(1-t) * x^t = x` for `0 < x < ⊤`. -/
lemma ennreal_rpow_add_identity {x : ENNReal} {t : ℝ}
    (hx_pos : 0 < x) (hx_top : x ≠ ⊤) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    x ^ (1 - t) * x ^ t = x := by
  let x' : ℝ := x.toReal
  have hx'_pos : 0 < x' := ENNReal.toReal_pos hx_pos.ne' hx_top
  have hx_eq : x = ENNReal.ofReal x' := (ENNReal.ofReal_toReal hx_top).symm
  have h1 : x ^ (1 - t) = ENNReal.ofReal (x' ^ (1 - t)) := by
    rw [hx_eq, ENNReal.ofReal_rpow_of_nonneg hx'_pos.le (by linarith)]
  have h2 : x ^ t = ENNReal.ofReal (x' ^ t) := by
    rw [hx_eq, ENNReal.ofReal_rpow_of_nonneg hx'_pos.le ht]
  rw [h1, h2]
  have h3 : 0 ≤ x' ^ (1 - t) := by positivity
  rw [← ENNReal.ofReal_mul h3]
  have h4 : x' ^ (1 - t) * x' ^ t = x' := by
    rw [← Real.rpow_add hx'_pos] <;> ring_nf <;> rw [Real.rpow_one]
  rw [h4, hx_eq]

/-- Key ENNReal identity: `(y / x)^t * x = x^(1-t) * y^t`. -/
lemma ennreal_div_rpow_mul {x y : ENNReal} {t : ℝ}
    (hx_pos : 0 < x) (hx_top : x ≠ ⊤) (hy_pos : 0 < y) (hy_top : y ≠ ⊤)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (y / x) ^ t * x = x ^ (1 - t) * y ^ t := by
  let x' : ℝ := x.toReal
  have hx'_pos : 0 < x' := ENNReal.toReal_pos hx_pos.ne' hx_top
  have hxt_pos : 0 < x ^ t := ENNReal.rpow_pos hx_pos hx_top
  have hxt_top : x ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht hx_top
  have h3 : x ^ t * x ^ (1 - t) = x := by
    have h_comm : x ^ t * x ^ (1 - t) = x ^ (1 - t) * x ^ t := by ring
    rw [h_comm]
    exact ennreal_rpow_add_identity hx_pos hx_top ht ht1
  have h1 : (y / x) ^ t = y ^ t * (x ^ t)⁻¹ := by
    have h11 : (y / x) ^ t = (y * x⁻¹) ^ t := by rw [div_eq_mul_inv]
    rw [h11]
    have h12 : (y * x⁻¹) ^ t = y ^ t * x⁻¹ ^ t := by
      rw [ENNReal.mul_rpow_of_nonneg] <;> positivity
    rw [h12]
    have h13 : x⁻¹ ^ t = (x ^ t)⁻¹ := by
      rw [← ENNReal.inv_rpow] <;> positivity
    rw [h13]
  rw [h1]
  calc y ^ t * (x ^ t)⁻¹ * x
    = y ^ t * ((x ^ t)⁻¹ * x) := by ring
  _ = y ^ t * ((x ^ t)⁻¹ * (x ^ t * x ^ (1 - t))) := by rw [h3]
  _ = y ^ t * (((x ^ t)⁻¹ * x ^ t) * x ^ (1 - t)) := by ring
  _ = y ^ t * (1 * x ^ (1 - t)) := by
    have h6 : (x ^ t)⁻¹ * x ^ t = 1 := ENNReal.inv_mul_cancel hxt_pos.ne' hxt_top
    rw [h6]
  _ = x ^ (1 - t) * y ^ t := by ring

/-- Strict monotonicity of ENNReal multiplication by positive finite element. -/
lemma ennreal_mul_lt_mul_left {a b c : ENNReal} (ha_pos : 0 < a) (ha_top : a ≠ ⊤) (h : b < c) :
    a * b < a * c := by
  by_contra h'
  have h'' : a * c ≤ a * b := le_of_not_gt h'
  have h3 : c ≤ b := by
    have h_eq1 : a⁻¹ * (a * c) = (a⁻¹ * a) * c := by rw [← mul_assoc]
    have h_eq2 : a⁻¹ * (a * b) = (a⁻¹ * a) * b := by rw [← mul_assoc]
    have h_cancel : a⁻¹ * a = 1 := ENNReal.inv_mul_cancel ha_pos.ne' ha_top
    calc c
      = a⁻¹ * (a * c) := by rw [h_eq1, h_cancel, one_mul]
    _ ≤ a⁻¹ * (a * b) := by gcongr
    _ = b := by rw [h_eq2, h_cancel, one_mul]
  exact not_le.mpr h h3

/-- Change of variables: `∫⁻ r in Ioi 0, F (c * r) = ofReal c⁻¹ * ∫⁻ s in Ioi 0, F s`. -/
lemma lintegral_comp_mul_pos {F : ℝ → ENNReal} (hF : Measurable F) {c : ℝ} (hc : 0 < c) :
    ∫⁻ (r : ℝ) in Ioi 0, F (c * r) = ENNReal.ofReal c⁻¹ * ∫⁻ (s : ℝ) in Ioi 0, F s := by
  let g : ℝ → ℝ := fun r => c * r
  have hg : Measurable g := measurable_const_mul c
  have hmap : Measure.map g (volume.restrict (Ioi 0)) =
      ENNReal.ofReal c⁻¹ • volume.restrict (Ioi 0) := by
    apply Measure.ext
    intro S hS
    have hgm : MeasurableSet (g ⁻¹' S) := hg hS
    have h1 : (Measure.map g (volume.restrict (Ioi 0))) S = volume (g ⁻¹' S ∩ Ioi 0) := by
      rw [Measure.map_apply hg hS, Measure.restrict_apply hgm] <;> rfl
    rw [h1]
    have h2 : g ⁻¹' S ∩ Ioi 0 = (fun x : ℝ => c⁻¹ * x) '' (S ∩ Ioi 0) := by
      ext x
      simp only [g, mem_inter_iff, mem_Ioi, mem_image]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨c * x, ⟨h1, mul_pos hc h2⟩, ?_⟩
        field_simp [hc.ne'] <;> ring
      · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
        constructor
        · have h_eq2 : c * (c⁻¹ * z) = z := by field_simp [hc.ne'] <;> ring
          simpa [h_eq2] using hz1
        · exact mul_pos (by positivity) hz2
    rw [h2]
    have h3 : MeasurableSet (S ∩ Ioi 0) := hS.inter measurableSet_Ioi
    have h4 : volume ((fun x : ℝ => c⁻¹ * x) '' (S ∩ Ioi 0)) =
        ENNReal.ofReal c⁻¹ * volume (S ∩ Ioi 0) := by
      have h5 : (fun x : ℝ => c⁻¹ * x) '' (S ∩ Ioi 0) = c⁻¹ • (S ∩ Ioi 0) := by
        ext z; simp [Set.mem_smul_set] <;> constructor <;> intro h <;> tauto
      rw [h5]
      exact volume_smul_real (show (0 : ℝ) < c⁻¹ by positivity) h3
    rw [h4]
    have h6 : (ENNReal.ofReal c⁻¹ • volume.restrict (Ioi 0)) S =
        ENNReal.ofReal c⁻¹ * volume (S ∩ Ioi 0) := by
      simp [Measure.restrict_apply hS] <;> ring
    exact h6.symm
  have h : ∫⁻ (s : ℝ), F s ∂(Measure.map g (volume.restrict (Ioi 0))) =
      ∫⁻ (r : ℝ), F (g r) ∂(volume.restrict (Ioi 0)) :=
    lintegral_map (μ := volume.restrict (Ioi 0)) hF hg
  rw [hmap] at h
  have h' : ∫⁻ (s : ℝ), F s ∂(ENNReal.ofReal c⁻¹ • volume.restrict (Ioi 0)) =
      ENNReal.ofReal c⁻¹ * ∫⁻ (s : ℝ) in Ioi 0, F s := by
    rw [lintegral_smul_measure] <;> rfl
  rw [h'] at h
  exact h.symm

/-- Layer cake for a bounded ENNReal function (finite everywhere). -/
lemma bounded_layer_cake {f : ℝ → ENNReal} (hf : Measurable f)
    {M : ENNReal} (hM_top : M ≠ ⊤) (h_bound : ∀ x, f x ≤ M) :
    ∫⁻ x, f x = ∫⁻ (s : ℝ) in Ioi 0, volume {x | f x > ENNReal.ofReal s} := by
  have h_ne_top : ∀ x, f x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top hM_top (h_bound x)
  let f_real : ℝ → ℝ := fun x => (f x).toReal
  have h_f_real_nn : ∀ x, 0 ≤ f_real x := fun x => by positivity
  have h_f_real_meas : Measurable f_real := hf.ennreal_toReal
  have h_f_eq : ∀ x, ENNReal.ofReal (f_real x) = f x := fun x =>
    ENNReal.ofReal_toReal (h_ne_top x)
  have h1 : ∫⁻ x, f x = ∫⁻ x, ENNReal.ofReal (f_real x) := by
    congr with x; exact (h_f_eq x).symm
  have h2 : ∫⁻ x, ENNReal.ofReal (f_real x) =
      ∫⁻ (s : ℝ) in Ioi 0, volume {x | s < f_real x} :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt volume
      (by filter_upwards with x; exact h_f_real_nn x) h_f_real_meas.aemeasurable
  have h3 : (fun s : ℝ => volume {x | s < f_real x}) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => volume {x | f x > ENNReal.ofReal s}) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos : 0 < s := hs
    have h4 : ∀ x, f x ≠ ⊤ := h_ne_top
    have h5 : {x | s < f_real x} = {x | f x > ENNReal.ofReal s} := by
      ext x
      have h6 : f x ≠ ⊤ := h4 x
      simp only [f_real, Set.mem_setOf_eq]
      have h7 : (ENNReal.ofReal s).toReal = s := by rw [ENNReal.toReal_ofReal hpos.le]
      have h8 : ((ENNReal.ofReal s).toReal < (f x).toReal) ↔ (ENNReal.ofReal s < f x) :=
        ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top h6
      rw [h7] at h8
      exact h8
    rw [h5]
  rw [h1, h2]
  exact lintegral_congr_ae h3

/-- Layer cake for h when ∫ h < ⊤ (so h < ⊤ a.e.). -/
lemma h_layer_cake {h : ℝ → ENNReal} (hh : Measurable h)
    (h_int_ne_top : ∫⁻ x, h x ≠ ⊤) :
    ∫⁻ x, h x = ∫⁻ (s : ℝ) in Ioi 0, volume {x | h x > ENNReal.ofReal s} := by
  have h_ae : ∀ᵐ x ∂volume, h x ≠ ⊤ := by
    by_contra h_contra
    let S : Set ℝ := {x | h x = ⊤}
    have hS_meas : MeasurableSet S := by
      have h1 : MeasurableSet ({⊤} : Set ENNReal) := measurableSet_singleton ⊤
      exact hh h1
    have hS_pos : 0 < volume S := by
      exact bot_lt_iff_ne_bot.mpr (show volume S ≠ 0 from by simpa [ae_iff] using h_contra)
    have h9 : ∫⁻ x, h x = ⊤ := by
      have h10 : ∫⁻ x, h x ≥ ∫⁻ x, Set.indicator S (fun _ => ⊤) x := by
        gcongr with x
        · by_cases hx : x ∈ S <;> simp [hx, Set.indicator_apply] <;> tauto
      have h11 : ∫⁻ x, Set.indicator S (fun _ => ⊤) x = ⊤ := by
        have h12 : ∫⁻ x, Set.indicator S (fun _ => ⊤) x = (⊤ : ENNReal) * volume S := by
          exact MeasureTheory.lintegral_indicator_const₀ hS_meas.nullMeasurableSet ⊤
        rw [h12]
        have h13 : (⊤ : ENNReal) * volume S = ⊤ := ENNReal.top_mul hS_pos.ne'
        exact h13
      rw [h11] at h10
      have h14 : ∫⁻ x, h x = ⊤ := by simpa using h10
      exact h14
    exact h_int_ne_top h9
  let h_real : ℝ → ℝ := fun x => (h x).toReal
  have h_h_real_nn : ∀ᵐ x ∂volume, 0 ≤ h_real x := by
    filter_upwards with x; positivity
  have h_h_real_meas : Measurable h_real := hh.ennreal_toReal
  have h_f_eq : ∀ᵐ x ∂volume, ENNReal.ofReal (h_real x) = h x := by
    filter_upwards [h_ae] with x hx
    exact ENNReal.ofReal_toReal hx
  have h1 : ∫⁻ x, h x = ∫⁻ x, ENNReal.ofReal (h_real x) := by
    rw [lintegral_congr_ae h_f_eq]
  have h2 : ∫⁻ x, ENNReal.ofReal (h_real x) =
      ∫⁻ (s : ℝ) in Ioi 0, volume {x | s < h_real x} :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt volume h_h_real_nn h_h_real_meas.aemeasurable
  have h3 : ∀ᵐ (s : ℝ) ∂volume.restrict (Ioi 0),
      volume {x | s < h_real x} = volume {x | h x > ENNReal.ofReal s} := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hpos : 0 < s := hs
    have h4 : ∀ᵐ x ∂volume, h x ≠ ⊤ := h_ae
    have h5 : {x | s < h_real x} =ᵐ[volume] {x | h x > ENNReal.ofReal s} := by
      filter_upwards [h4] with x hx
      have h6 : (s < (h x).toReal) ↔ (ENNReal.ofReal s < h x) := by
        have h7 : (ENNReal.ofReal s).toReal = s := by rw [ENNReal.toReal_ofReal hpos.le]
        have h8 : ((ENNReal.ofReal s).toReal < (h x).toReal) ↔ (ENNReal.ofReal s < h x) :=
          ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hx
        rw [h7] at h8
        exact h8
      have h9 : (s < h_real x) ↔ (ENNReal.ofReal s < h x) := by
        simpa [h_real] using h6
      exact propext h9
    exact measure_congr h5
  rw [h1, h2]
  exact lintegral_congr_ae h3


/-! ### Bounded 1D PL -/

/-- **1D Prékopa–Leindler for bounded f, g.** -/
theorem prekopa_leindler_one_dim_bounded {f g h : ℝ → ENNReal}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {t : ℝ} (ht1 : 0 < t) (ht2 : t < 1)
    (hpl : ∀ x y, h ((1 - t) * x + t * y) ≥ f x ^ (1 - t) * g y ^ t)
    {M_bound N_bound : ENNReal}
    (hM_bound : ∀ x, f x ≤ M_bound) (hN_bound : ∀ x, g x ≤ N_bound)
    (hM_top : M_bound ≠ ⊤) (hN_top : N_bound ≠ ⊤) :
    ∫⁻ x, h x ≥ (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t := by
  let M : ENNReal := sSup (Set.range f)
  let N : ENNReal := sSup (Set.range g)
  have hM_ub : ∀ y ∈ Set.range f, y ≤ M_bound := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hM_bound x
  have hN_ub : ∀ y ∈ Set.range g, y ≤ N_bound := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hN_bound x
  have hM_nonempty : (Set.range f).Nonempty := ⟨f 0, by simp⟩
  have hN_nonempty : (Set.range g).Nonempty := ⟨g 0, by simp⟩
  have hM_le : M ≤ M_bound := csSup_le hM_nonempty hM_ub
  have hN_le : N ≤ N_bound := csSup_le hN_nonempty hN_ub
  have hM_top' : M ≠ ⊤ := ne_top_of_le_ne_top hM_top hM_le
  have hN_top' : N ≠ ⊤ := ne_top_of_le_ne_top hN_top hN_le
  have hM_all : ∀ x, f x ≤ M := fun x =>
    le_csSup ⟨M_bound, hM_ub⟩ (by simp [M])
  have hN_all : ∀ x, g x ≤ N := fun x =>
    le_csSup ⟨N_bound, hN_ub⟩ (by simp [N])

  by_cases hM0 : M = 0
  · have hf0 : ∀ x, f x = 0 := fun x => by
      have h : f x ≤ M := hM_all x
      rw [hM0] at h
      simpa using h
    have hint : ∫⁻ x, f x = 0 := by
      have h : f = 0 := funext hf0
      rw [h]; simp
    rw [hint]
    have h : (0 : ENNReal) ^ (1 - t) = 0 := ENNReal.zero_rpow_of_pos (by linarith)
    rw [h] <;> simp
  by_cases hN0 : N = 0
  · have hg0 : ∀ x, g x = 0 := fun x => by
      have h : g x ≤ N := hN_all x
      rw [hN0] at h
      simpa using h
    have hint : ∫⁻ y, g y = 0 := by
      have h : g = 0 := funext hg0
      rw [h]; simp
    rw [hint]
    have h : (0 : ENNReal) ^ t = 0 := ENNReal.zero_rpow_of_pos ht1
    rw [h] <;> simp

  have hM_pos : 0 < M := Ne.bot_lt hM0
  have hN_pos : 0 < N := Ne.bot_lt hN0
  have h1pos : 0 < 1 - t := by linarith

  set a_er : ENNReal := (M / N) ^ t with ha_er_def
  set b_er : ENNReal := (N / M) ^ (1 - t) with hb_er_def
  set a : ℝ := a_er.toReal with ha_def
  set b : ℝ := b_er.toReal with hb_def

  have hMN_pos : 0 < M / N := by
    have hN_inv_pos : 0 < N⁻¹ := ENNReal.inv_pos.mpr hN_top'
    have h : M / N = M * N⁻¹ := by
      simp [div_eq_mul_inv]
    rw [h]
    exact ENNReal.mul_pos hM_pos.ne' hN_inv_pos.ne'
  have hNM_pos : 0 < N / M := by
    have hM_inv_pos : 0 < M⁻¹ := ENNReal.inv_pos.mpr hM_top'
    have h : N / M = N * M⁻¹ := by
      simp [div_eq_mul_inv]
    rw [h]
    exact ENNReal.mul_pos hN_pos.ne' hM_inv_pos.ne'
  have hMN_top : M / N ≠ ⊤ := (ENNReal.div_lt_top hM_top' hN_pos.ne').ne
  have hNM_top : N / M ≠ ⊤ := (ENNReal.div_lt_top hN_top' hM_pos.ne').ne
  have ha_er_pos : 0 < a_er := by
    simpa [ha_er_def] using ENNReal.rpow_pos hMN_pos hMN_top
  have hb_er_pos : 0 < b_er := by
    simpa [hb_er_def] using ENNReal.rpow_pos hNM_pos hNM_top
  have ha_er_top : a_er ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ht1.le hMN_top
  have hb_er_top : b_er ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg h1pos.le hNM_top
  have ha_pos : 0 < a := ENNReal.toReal_pos ha_er_pos.ne' ha_er_top
  have hb_pos : 0 < b := ENNReal.toReal_pos hb_er_pos.ne' hb_er_top

  have hMN_inv : (M / N) * (N / M) = 1 := by
    have h7 : (M / N) * (N / M) = (M * N⁻¹) * (N * M⁻¹) := by
      simp [div_eq_mul_inv] <;> ring
    rw [h7]
    have h8 : (M * N⁻¹) * (N * M⁻¹) = M * (N⁻¹ * N) * M⁻¹ := by ring
    rw [h8]
    have h9 : N⁻¹ * N = 1 := ENNReal.inv_mul_cancel hN_pos.ne' hN_top'
    rw [h9]
    have h10 : M * (1 : ENNReal) * M⁻¹ = M * M⁻¹ := by ring
    rw [h10]
    exact ENNReal.mul_inv_cancel hM_pos.ne' hM_top'
  have hab : a_er ^ (1 - t) * b_er ^ t = 1 := by
    have h3 : a_er ^ (1 - t) = (M / N) ^ (t * (1 - t)) := by
      rw [ha_er_def, ← ENNReal.rpow_mul] <;> ring
    have h4 : b_er ^ t = (N / M) ^ (t * (1 - t)) := by
      rw [hb_er_def, ← ENNReal.rpow_mul] <;> ring_nf
    rw [h3, h4]
    have h5 : (M / N) ^ (t * (1 - t)) * (N / M) ^ (t * (1 - t)) =
        ((M / N) * (N / M)) ^ (t * (1 - t)) := by
      rw [← ENNReal.mul_rpow_of_nonneg] <;> positivity
    rw [h5, hMN_inv] <;> simp

  set r₀ : ENNReal := M ^ (1 - t) * N ^ t with hr₀_def
  let F : ENNReal → ENNReal := fun s => volume {x | f x > s}
  let G : ENNReal → ENNReal := fun tval => volume {y | g y > tval}
  let H : ENNReal → ENNReal := fun r => volume {z | h z > r}

  have h_antitone_F : Antitone (fun r : ℝ => F (ENNReal.ofReal r)) := by
    intro r s hrs
    apply measure_mono
    intro x hx
    have h5 : ENNReal.ofReal r ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal hrs
    exact h5.trans_lt hx
  have h_antitone_G : Antitone (fun r : ℝ => G (ENNReal.ofReal r)) := by
    intro r s hrs
    apply measure_mono
    intro x hx
    have h5 : ENNReal.ofReal r ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal hrs
    exact h5.trans_lt hx
  have h_meas_F : Measurable (fun r : ℝ => F (ENNReal.ofReal r)) := h_antitone_F.measurable
  have h_meas_G : Measurable (fun r : ℝ => G (ENNReal.ofReal r)) := h_antitone_G.measurable

  have h_a_er_inv_M : a_er⁻¹ * M = r₀ := by
    have h22 : (M / N)⁻¹ = N / M := by
      have h_pos : 0 < M / N := hMN_pos
      have h_top : M / N ≠ ⊤ := hMN_top
      calc (M / N)⁻¹
        = (M / N)⁻¹ * ((M / N) * (N / M)) := by rw [hMN_inv] <;> simp
      _ = ((M / N)⁻¹ * (M / N)) * (N / M) := by ring
      _ = 1 * (N / M) := by rw [ENNReal.inv_mul_cancel h_pos.ne' h_top]
      _ = N / M := by ring
    have h1 : a_er⁻¹ = (N / M) ^ t := by
      rw [ha_er_def]
      have h21 : ((M / N) ^ t)⁻¹ = (M / N)⁻¹ ^ t := by
        rw [← ENNReal.inv_rpow] <;> positivity
      rw [h21, h22]
    rw [h1]
    exact ennreal_div_rpow_mul hM_pos hM_top' hN_pos hN_top' ht1.le ht2.le
  have h_b_er_inv_N : b_er⁻¹ * N = r₀ := by
    have h22 : (N / M)⁻¹ = M / N := by
      have h_pos : 0 < N / M := hNM_pos
      have h_top : N / M ≠ ⊤ := hNM_top
      have h_prod : (N / M) * (M / N) = 1 := by
        rw [mul_comm, hMN_inv]
      calc (N / M)⁻¹
        = (N / M)⁻¹ * ((N / M) * (M / N)) := by rw [h_prod] <;> simp
      _ = ((N / M)⁻¹ * (N / M)) * (M / N) := by ring
      _ = 1 * (M / N) := by rw [ENNReal.inv_mul_cancel h_pos.ne' h_top]
      _ = M / N := by ring
    have h1 : b_er⁻¹ = (M / N) ^ (1 - t) := by
      rw [hb_er_def]
      have h21 : ((N / M) ^ (1 - t))⁻¹ = (N / M)⁻¹ ^ (1 - t) := by
        rw [← ENNReal.inv_rpow] <;> positivity
      rw [h21, h22]
    rw [h1]
    have h := ennreal_div_rpow_mul hN_pos hN_top' hM_pos hM_top' h1pos.le (show (1 - t) ≤ 1 by linarith)
    have h_exp : 1 - (1 - t) = t := by ring
    rw [h_exp] at h
    have h_comm : N ^ t * M ^ (1 - t) = M ^ (1 - t) * N ^ t := by ring
    rw [h_comm] at h
    exact h

  have h_er0_eq : a_er * r₀ = M := by
    have h_cancel : a_er * (a_er⁻¹ * M) = M := by
      have h : a_er * (a_er⁻¹ * M) = (a_er * a_er⁻¹) * M := by rw [← mul_assoc]
      rw [h, ENNReal.mul_inv_cancel ha_er_pos.ne' ha_er_top, one_mul]
    calc a_er * r₀
      = a_er * (a_er⁻¹ * M) := by rw [h_a_er_inv_M]
    _ = M := h_cancel

  have h_strict_mono : ∀ {x y : ENNReal}, a_er * x < a_er * y ↔ x < y := by
    intro x y
    constructor
    · intro h
      by_contra h'
      have h'' : y ≤ x := le_of_not_gt h'
      have h3 : a_er * y ≤ a_er * x := by gcongr
      exact not_le.mpr h h3
    · intro h
      exact ennreal_mul_lt_mul_left ha_er_pos ha_er_top h
  have thresh_lt : ∀ (r' : ENNReal), (a_er * r' < M) ↔ (r' < r₀) := by
    intro r'
    have h : a_er * r' < a_er * r₀ ↔ r' < r₀ := h_strict_mono
    rw [h_er0_eq] at h
    exact h
  have thresh_gt : ∀ (r' : ENNReal), (a_er * r' > M) ↔ (r' > r₀) := by
    intro r'
    have h : a_er * r' > a_er * r₀ ↔ r' > r₀ := h_strict_mono
    rw [h_er0_eq] at h
    exact h

  have h_a_conv : ∀ (r : ℝ), a_er * ENNReal.ofReal r = ENNReal.ofReal (a * r) := by
    intro r
    have h_a_er_ofReal : a_er = ENNReal.ofReal a := by
      simp [a, ha_def, ENNReal.ofReal_toReal ha_er_top]
    rw [h_a_er_ofReal, ← ENNReal.ofReal_mul (show 0 ≤ a by linarith)]
    <;> ring
  have h_b_conv : ∀ (r : ℝ), b_er * ENNReal.ofReal r = ENNReal.ofReal (b * r) := by
    intro r
    have h_b_er_ofReal : b_er = ENNReal.ofReal b := by
      simp [b, hb_def, ENNReal.ofReal_toReal hb_er_top]
    rw [h_b_er_ofReal, ← ENNReal.ofReal_mul (show 0 ≤ b by linarith)]
    <;> ring

  have h_main_ae : ∀ᵐ (r : ℝ) ∂volume.restrict (Ioi 0),
      H (ENNReal.ofReal r) ≥
        ENNReal.ofReal (1 - t) * F (a_er * ENNReal.ofReal r) +
        ENNReal.ofReal t * G (b_er * ENNReal.ofReal r) := by
    let S : Set ℝ := {r | a_er * ENNReal.ofReal r = M}
    have hS_meas : MeasurableSet S := by
      have hgm : Measurable (fun r : ℝ => a_er * ENNReal.ofReal r) := by fun_prop
      exact hgm (measurableSet_singleton M)
    have hS_sub : S.Subsingleton := by
      intro r1 hr1 r2 hr2
      have h_eq1 : a_er * ENNReal.ofReal r1 = M := hr1
      have h_eq2 : a_er * ENNReal.ofReal r2 = M := hr2
      have h : a_er * ENNReal.ofReal r1 = a_er * ENNReal.ofReal r2 := h_eq1.trans h_eq2.symm
      have h_cancel1 : a_er⁻¹ * (a_er * ENNReal.ofReal r1) = ENNReal.ofReal r1 := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha_er_pos.ne' ha_er_top, one_mul]
      have h_cancel2 : a_er⁻¹ * (a_er * ENNReal.ofReal r2) = ENNReal.ofReal r2 := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha_er_pos.ne' ha_er_top, one_mul]
      have h' : a_er⁻¹ * (a_er * ENNReal.ofReal r1) = a_er⁻¹ * (a_er * ENNReal.ofReal r2) := by rw [h]
      have h_cancel : ENNReal.ofReal r1 = ENNReal.ofReal r2 := by
        rw [h_cancel1, h_cancel2] at h'
        exact h'
      have h_r1_nonneg : 0 ≤ r1 := by
        by_contra h_neg
        have h' : ENNReal.ofReal r1 = 0 := by
          rw [ENNReal.ofReal_eq_zero] <;> linarith
        rw [h'] at h_eq1
        simp [ha_er_pos.ne'] at h_eq1 <;> tauto
      have h_r2_nonneg : 0 ≤ r2 := by
        by_contra h_neg
        have h' : ENNReal.ofReal r2 = 0 := by
          rw [ENNReal.ofReal_eq_zero] <;> linarith
        rw [h'] at h_eq2
        simp [ha_er_pos.ne'] at h_eq2 <;> tauto
      have h_eq : r1 = r2 := by
        have h1 : (ENNReal.ofReal r1).toReal = (ENNReal.ofReal r2).toReal := by rw [h_cancel]
        have h2 : (ENNReal.ofReal r1).toReal = r1 := by
          rw [ENNReal.toReal_ofReal h_r1_nonneg]
        have h3 : (ENNReal.ofReal r2).toReal = r2 := by
          rw [ENNReal.toReal_ofReal h_r2_nonneg]
        rw [h2, h3] at h1
        exact h1
      exact h_eq
    have hS_null : volume S = 0 := by
      have h_eq_empty_or_singleton : S = ∅ ∨ ∃ (x : ℝ), S = {x} :=
        hS_sub.eq_empty_or_singleton
      rcases h_eq_empty_or_singleton with (h_empty | ⟨x, h_x⟩)
      · rw [h_empty] <;> simp
      · rw [h_x] <;> simp
    have h_null : volume.restrict (Ioi 0) S = 0 := by
      rw [Measure.restrict_apply hS_meas]
      have h_inter : S ∩ Ioi 0 ⊆ S := by simp
      have h : volume (S ∩ Ioi 0) ≤ volume S := measure_mono h_inter
      rw [hS_null] at h
      exact bot_unique h
    have h_ae_ne : ∀ᵐ (r : ℝ) ∂volume.restrict (Ioi 0), a_er * ENNReal.ofReal r ≠ M := by
      rw [ae_iff]
      have h_set : {r : ℝ | ¬(a_er * ENNReal.ofReal r ≠ M)} = S := by
        ext r
        simp [S]
        <;> tauto
      rw [h_set]
      exact h_null
    filter_upwards [h_ae_ne, ae_restrict_mem measurableSet_Ioi] with r hr_ne hr_pos
    set r' : ENNReal := ENNReal.ofReal r with hr'_def
    have hr'_pos : 0 < r' := by
      rw [hr'_def]
      exact ENNReal.ofReal_pos.mpr hr_pos
    have hne : a_er * r' ≠ M := by simpa [hr'_def] using hr_ne
    have h_cases : a_er * r' < M ∨ a_er * r' > M := lt_or_gt_of_ne hne
    rcases h_cases with (h_lt | h_gt)
    · -- Both level sets nonempty
      have hb_lt : b_er * r' < N := by
        have h_r0 : r' < r₀ := (thresh_lt r').mp h_lt
        have h_cancel : b_er * (b_er⁻¹ * N) = N := by
          have h : b_er * (b_er⁻¹ * N) = (b_er * b_er⁻¹) * N := by rw [← mul_assoc]
          rw [h, ENNReal.mul_inv_cancel hb_er_pos.ne' hb_er_top, one_mul]
        calc b_er * r'
          < b_er * r₀ := by gcongr
        _ = b_er * (b_er⁻¹ * N) := by rw [h_b_er_inv_N]
        _ = N := h_cancel
      let A : Set ℝ := {x | f x > a_er * r'}
      let B : Set ℝ := {y | g y > b_er * r'}
      have hA_meas : MeasurableSet A := hf (show MeasurableSet (Ioi (a_er * r')) from measurableSet_Ioi)
      have hB_meas : MeasurableSet B := hg (show MeasurableSet (Ioi (b_er * r')) from measurableSet_Ioi)
      have hA_ne : A.Nonempty := by
        by_contra h
        have h' : A = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        have h_all : ∀ x, f x ≤ a_er * r' := by
          intro x
          by_contra hfx
          have h_in_A : x ∈ A := by simpa [A] using hfx
          rw [h'] at h_in_A <;> tauto
        have h_ub : ∀ y ∈ Set.range f, y ≤ a_er * r' := by
          intro y hy
          rcases hy with ⟨x, rfl⟩
          exact h_all x
        have h_le : M ≤ a_er * r' := csSup_le hM_nonempty h_ub
        exact not_le.mpr h_lt h_le
      have hB_ne : B.Nonempty := by
        by_contra h
        have h' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp h
        have h_all : ∀ x, g x ≤ b_er * r' := by
          intro x
          by_contra hfx
          have h_in_B : x ∈ B := by simpa [B] using hfx
          rw [h'] at h_in_B <;> tauto
        have h_ub : ∀ y ∈ Set.range g, y ≤ b_er * r' := by
          intro y hy
          rcases hy with ⟨x, rfl⟩
          exact h_all x
        have h_le : N ≤ b_er * r' := csSup_le hN_nonempty h_ub
        exact not_le.mpr hb_lt h_le
      let C : Set ℝ := (1 - t : ℝ) • A
      let D : Set ℝ := (t : ℝ) • B
      have hC_meas : MeasurableSet C := hA_meas.const_smul_of_ne_zero (show (1 - t : ℝ) ≠ 0 by linarith)
      have hD_meas : MeasurableSet D := hB_meas.const_smul_of_ne_zero (show (t : ℝ) ≠ 0 by linarith)
      have hC_ne : C.Nonempty := hA_ne.image _
      have hD_ne : D.Nonempty := hB_ne.image _
      have h_bm : volume (C + D) ≥ volume C + volume D :=
        brunnMinkowski_oneDim C D hC_meas hD_meas hC_ne hD_ne
      have h_vol_C : volume C = ENNReal.ofReal (1 - t) * F (a_er * r') := by
        simpa [C, F] using volume_smul_real h1pos hA_meas
      have h_vol_D : volume D = ENNReal.ofReal t * G (b_er * r') := by
        simpa [D, G] using volume_smul_real ht1 hB_meas
      have h_inclusion : C + D ⊆ {z | h z > r'} := by
        intro z hz
        rcases hz with ⟨c, hc, d, hd, rfl⟩
        rcases hc with ⟨x, hx, rfl⟩
        rcases hd with ⟨y, hy, rfl⟩
        have hfx : f x > a_er * r' := by simpa [A] using hx
        have hgy : g y > b_er * r' := by simpa [B] using hy
        have h1 : f x ^ (1 - t) * g y ^ t > (a_er * r') ^ (1 - t) * (b_er * r') ^ t := by
          have h2 : f x ^ (1 - t) > (a_er * r') ^ (1 - t) := ENNReal.rpow_lt_rpow hfx h1pos
          have h3 : g y ^ t > (b_er * r') ^ t := ENNReal.rpow_lt_rpow hgy ht1
          have h_fx_top : f x ^ (1 - t) ≠ ⊤ :=
            ENNReal.rpow_ne_top_of_nonneg (by linarith) (ne_top_of_le_ne_top hM_top' (hM_all x))
          have h_br_top : (b_er * r') ^ t ≠ ⊤ :=
            ENNReal.rpow_ne_top_of_nonneg ht1.le (mul_ne_top hb_er_top ENNReal.ofReal_ne_top)
          have h_aer_r'_pos : 0 < a_er * r' := ENNReal.mul_pos ha_er_pos.ne' hr'_pos.ne'
          have h_fx_pos' : 0 < f x := lt_trans h_aer_r'_pos hfx
          have h_pos1 : 0 < f x ^ (1 - t) :=
            ENNReal.rpow_pos h_fx_pos' (ne_top_of_le_ne_top hM_top' (hM_all x))
          have h_strict1 : f x ^ (1 - t) * g y ^ t > f x ^ (1 - t) * (b_er * r') ^ t :=
            ennreal_mul_lt_mul_left h_pos1 h_fx_top h3
          have h_br_pos' : 0 < (b_er * r') ^ t := by positivity
          have h_strict2 : f x ^ (1 - t) * (b_er * r') ^ t > (a_er * r') ^ (1 - t) * (b_er * r') ^ t := by
            have h : (b_er * r') ^ t * f x ^ (1 - t) > (b_er * r') ^ t * (a_er * r') ^ (1 - t) :=
              ennreal_mul_lt_mul_left h_br_pos' h_br_top h2
            have h_comm1 : (b_er * r') ^ t * f x ^ (1 - t) = f x ^ (1 - t) * (b_er * r') ^ t := by ring
            have h_comm2 : (b_er * r') ^ t * (a_er * r') ^ (1 - t) = (a_er * r') ^ (1 - t) * (b_er * r') ^ t := by ring
            rw [h_comm1, h_comm2] at h
            exact h
          calc f x ^ (1 - t) * g y ^ t
            > f x ^ (1 - t) * (b_er * r') ^ t := h_strict1
          _ > (a_er * r') ^ (1 - t) * (b_er * r') ^ t := h_strict2
        have h4 : (a_er * r') ^ (1 - t) * (b_er * r') ^ t = r' := by
          have h5 : (a_er * r') ^ (1 - t) = a_er ^ (1 - t) * r' ^ (1 - t) := by
            rw [ENNReal.mul_rpow_of_nonneg] <;> positivity
          have h6 : (b_er * r') ^ t = b_er ^ t * r' ^ t := by
            rw [ENNReal.mul_rpow_of_nonneg] <;> positivity
          rw [h5, h6]
          have h7 : a_er ^ (1 - t) * r' ^ (1 - t) * (b_er ^ t * r' ^ t) =
              (a_er ^ (1 - t) * b_er ^ t) * (r' ^ (1 - t) * r' ^ t) := by ring
          rw [h7, hab]
          have h8 : r' ^ (1 - t) * r' ^ t = r' :=
            ennreal_rpow_add_identity hr'_pos ENNReal.ofReal_ne_top ht1.le ht2.le
          rw [h8] <;> ring
        have h9 : h ((1 - t) * x + t * y) ≥ f x ^ (1 - t) * g y ^ t := hpl x y
        have h1' : f x ^ (1 - t) * g y ^ t > r' := by
          rw [h4] at h1
          exact h1
        have h10 : h ((1 - t) * x + t * y) > r' := lt_of_lt_of_le h1' h9
        simpa using h10
      have h5 : H r' ≥ volume (C + D) := measure_mono h_inclusion
      calc H r' ≥ volume (C + D) := h5
           _ ≥ volume C + volume D := h_bm
           _ = ENNReal.ofReal (1 - t) * F (a_er * r') + ENNReal.ofReal t * G (b_er * r') := by
             rw [h_vol_C, h_vol_D] <;> ring
    · -- Both level sets empty
      have hb_gt : b_er * r' > N := by
        have h_r0 : r' > r₀ := (thresh_gt r').mp h_gt
        have h_cancel : b_er * (b_er⁻¹ * N) = N := by
          have h : b_er * (b_er⁻¹ * N) = (b_er * b_er⁻¹) * N := by rw [← mul_assoc]
          rw [h, ENNReal.mul_inv_cancel hb_er_pos.ne' hb_er_top, one_mul]
        calc b_er * r'
          > b_er * r₀ := by gcongr
        _ = b_er * (b_er⁻¹ * N) := by rw [h_b_er_inv_N]
        _ = N := h_cancel
      have hF_empty : F (a_er * r') = 0 := by
        have h : ∀ x, f x ≤ a_er * r' := fun x => (hM_all x).trans h_gt.le
        have h' : {x : ℝ | f x > a_er * r'} = ∅ := by
          ext x
          simp only [mem_setOf_eq, mem_empty_iff_false]
          have h_le : f x ≤ a_er * r' := h x
          have h_not : ¬(f x > a_er * r') := not_lt.mpr h_le
          exact ⟨fun h => h_not h, fun h => False.elim h⟩
        simpa [F] using congr_arg volume h'
      have hG_empty : G (b_er * r') = 0 := by
        have h : ∀ x, g x ≤ b_er * r' := fun x => (hN_all x).trans hb_gt.le
        have h' : {x : ℝ | g x > b_er * r'} = ∅ := by
          ext x
          simp only [mem_setOf_eq, mem_empty_iff_false]
          have h_le : g x ≤ b_er * r' := h x
          have h_not : ¬(g x > b_er * r') := not_lt.mpr h_le
          exact ⟨fun h => h_not h, fun h => False.elim h⟩
        simpa [G] using congr_arg volume h'
      rw [hF_empty, hG_empty] <;> simp

  have h_integral : ∫⁻ (r : ℝ) in Ioi 0, H (ENNReal.ofReal r) ≥
      (ENNReal.ofReal (1 - t) * (∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r))) +
      (ENNReal.ofReal t * (∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r))) := by
    have h : ∫⁻ (r : ℝ) in Ioi 0, H (ENNReal.ofReal r) ≥
        ∫⁻ (r : ℝ) in Ioi 0, (ENNReal.ofReal (1 - t) * F (a_er * ENNReal.ofReal r) +
          ENNReal.ofReal t * G (b_er * ENNReal.ofReal r)) :=
      lintegral_mono_ae h_main_ae
    let F' : ℝ → ENNReal := fun r => ENNReal.ofReal (1 - t) * F (a_er * ENNReal.ofReal r)
    let G' : ℝ → ENNReal := fun r => ENNReal.ofReal t * G (b_er * ENNReal.ofReal r)
    have hFa_meas : Measurable (fun r : ℝ => F (a_er * ENNReal.ofReal r)) := by
      have h_eq : (fun r : ℝ => F (a_er * ENNReal.ofReal r)) = (fun r : ℝ => F (ENNReal.ofReal (a * r))) := by
        funext r
        exact congr_arg F (h_a_conv r)
      rw [h_eq]
      exact h_meas_F.comp (measurable_const_mul a)
    have hGb_meas : Measurable (fun r : ℝ => G (b_er * ENNReal.ofReal r)) := by
      have h_eq : (fun r : ℝ => G (b_er * ENNReal.ofReal r)) = (fun r : ℝ => G (ENNReal.ofReal (b * r))) := by
        funext r
        exact congr_arg G (h_b_conv r)
      rw [h_eq]
      exact h_meas_G.comp (measurable_const_mul b)
    have hF'_meas : Measurable F' := hFa_meas.const_mul _
    have hG'_meas : Measurable G' := hGb_meas.const_mul _
    have h2 : ∫⁻ (r : ℝ) in Ioi 0, F' r + G' r =
        (∫⁻ (r : ℝ) in Ioi 0, F' r) + (∫⁻ (r : ℝ) in Ioi 0, G' r) := by
      exact MeasureTheory.lintegral_add_left hF'_meas G'
    have h2F : ∫⁻ (r : ℝ) in Ioi 0, F' r =
        ENNReal.ofReal (1 - t) * (∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r)) := by
      rw [lintegral_const_mul'] <;> simp
    have h2G : ∫⁻ (r : ℝ) in Ioi 0, G' r =
        ENNReal.ofReal t * (∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r)) := by
      rw [lintegral_const_mul'] <;> simp
    rw [h2, h2F, h2G] at h
    exact h

  have hFa : ∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r) =
      a_er⁻¹ * ∫⁻ (s : ℝ) in Ioi 0, F (ENNReal.ofReal s) := by
    have h3 : ∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r) =
        ∫⁻ (r : ℝ) in Ioi 0, F (ENNReal.ofReal (a * r)) := by
      apply lintegral_congr
      intro r
      exact congr_arg F (h_a_conv r)
    rw [h3]
    have h4 := lintegral_comp_mul_pos h_meas_F ha_pos
    have h5 : ENNReal.ofReal a⁻¹ = a_er⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos ha_pos, ← ENNReal.ofReal_toReal ha_er_top] <;> rfl
    rw [h5] at h4
    exact h4
  have hGb : ∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r) =
      b_er⁻¹ * ∫⁻ (t : ℝ) in Ioi 0, G (ENNReal.ofReal t) := by
    have h3 : ∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r) =
        ∫⁻ (r : ℝ) in Ioi 0, G (ENNReal.ofReal (b * r)) := by
      apply lintegral_congr
      intro r
      exact congr_arg G (h_b_conv r)
    rw [h3]
    have h4 := lintegral_comp_mul_pos h_meas_G hb_pos
    have h5 : ENNReal.ofReal b⁻¹ = b_er⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hb_pos, ← ENNReal.ofReal_toReal hb_er_top] <;> rfl
    rw [h5] at h4
    exact h4

  -- Layer cakes for f and g (bounded)
  have h_layer_f : ∫⁻ x, f x = ∫⁻ (s : ℝ) in Ioi 0, F (ENNReal.ofReal s) :=
    bounded_layer_cake hf hM_top hM_bound
  have h_layer_g : ∫⁻ y, g y = ∫⁻ (t : ℝ) in Ioi 0, G (ENNReal.ofReal t) :=
    bounded_layer_cake hg hN_top hN_bound

  by_cases hh_top : ∫⁻ x, h x = ⊤
  · rw [hh_top]
    exact le_top
  · have h_layer_h : ∫⁻ z, h z = ∫⁻ (r : ℝ) in Ioi 0, H (ENNReal.ofReal r) :=
      h_layer_cake hh hh_top
    let X := ∫⁻ x, f x
    let Y := ∫⁻ y, g y
    have h1Fa : ∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r) = a_er⁻¹ * X := by
      rw [hFa, ←h_layer_f]
    have h1Gb : ∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r) = b_er⁻¹ * Y := by
      rw [hGb, ←h_layer_g]
    let f_sum (u v : ENNReal) : ENNReal :=
      ENNReal.ofReal (1 - t) * u + ENNReal.ofReal t * v
    have h_rhs_eq : f_sum (∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r))
          (∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r)) =
        f_sum (a_er⁻¹ * X) (b_er⁻¹ * Y) := by
      calc
        f_sum (∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r))
            (∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r))
          = f_sum (a_er⁻¹ * X) (∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r)) :=
            congr_arg (fun x => f_sum x (∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r))) h1Fa
        _ = f_sum (a_er⁻¹ * X) (b_er⁻¹ * Y) :=
            congr_arg (fun y => f_sum (a_er⁻¹ * X) y) h1Gb
    have h_final1 : ∫⁻ (r : ℝ) in Ioi 0, H (ENNReal.ofReal r) ≥
        f_sum (a_er⁻¹ * X) (b_er⁻¹ * Y) := by
      have h : ∫⁻ (r : ℝ) in Ioi 0, H (ENNReal.ofReal r) ≥
          f_sum (∫⁻ (r : ℝ) in Ioi 0, F (a_er * ENNReal.ofReal r))
              (∫⁻ (r : ℝ) in Ioi 0, G (b_er * ENNReal.ofReal r)) := h_integral
      rw [h_rhs_eq] at h
      exact h
    have h_am_gm : ENNReal.ofReal (1 - t) * (a_er⁻¹ * X) + ENNReal.ofReal t * (b_er⁻¹ * Y) ≥
        X ^ (1 - t) * Y ^ t := by
      have h10 : (a_er⁻¹ * X) ^ (1 - t) = a_er⁻¹ ^ (1 - t) * X ^ (1 - t) := by
        rw [ENNReal.mul_rpow_of_nonneg] <;> positivity
      have h11 : (b_er⁻¹ * Y) ^ t = b_er⁻¹ ^ t * Y ^ t := by
        rw [ENNReal.mul_rpow_of_nonneg] <;> positivity
      have h12 : a_er⁻¹ ^ (1 - t) * b_er⁻¹ ^ t = 1 := by
        have h13 : a_er⁻¹ ^ (1 - t) = (a_er ^ (1 - t))⁻¹ :=
          ENNReal.inv_rpow a_er (1 - t)
        have h14 : b_er⁻¹ ^ t = (b_er ^ t)⁻¹ :=
          ENNReal.inv_rpow b_er t
        rw [h13, h14]
        set x := a_er ^ (1 - t) with hx_def
        set y := b_er ^ t with hy_def
        have hxy : x * y = 1 := hab
        have hx_pos : 0 < x := by positivity
        have hx_top : x ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) ha_er_top
        have hy_pos : 0 < y := by positivity
        have hy_top : y ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht1.le hb_er_top
        have hx_inv : x⁻¹ = y := by
          calc x⁻¹
            = x⁻¹ * (x * y) := by rw [hxy] <;> simp
          _ = (x⁻¹ * x) * y := by ring
          _ = 1 * y := by rw [ENNReal.inv_mul_cancel hx_pos.ne' hx_top]
          _ = y := by ring
        have hy_inv : y⁻¹ = x := by
          calc y⁻¹
            = y⁻¹ * (x * y) := by rw [hxy] <;> simp
          _ = (y⁻¹ * y) * x := by ring
          _ = 1 * x := by rw [ENNReal.inv_mul_cancel hy_pos.ne' hy_top]
          _ = x := by ring
        have h15 : x⁻¹ * y⁻¹ = 1 := by
          rw [hx_inv, hy_inv]
          have h16 : y * x = x * y := by ring
          rw [h16, hxy]
        exact h15
      have h9 : X ^ (1 - t) * Y ^ t = (a_er⁻¹ * X) ^ (1 - t) * (b_er⁻¹ * Y) ^ t := by
        calc X ^ (1 - t) * Y ^ t
          = 1 * (X ^ (1 - t) * Y ^ t) := by simp
        _ = (a_er⁻¹ ^ (1 - t) * b_er⁻¹ ^ t) * (X ^ (1 - t) * Y ^ t) := by rw [h12]
        _ = a_er⁻¹ ^ (1 - t) * X ^ (1 - t) * (b_er⁻¹ ^ t * Y ^ t) := by ring
        _ = (a_er⁻¹ * X) ^ (1 - t) * (b_er⁻¹ * Y) ^ t := by rw [h10, h11] <;> ring
      rw [h9]
      exact ennreal_weighted_am_gm ht1 ht2
    have h_result : ∫⁻ (r : ℝ) in Ioi 0, H (ENNReal.ofReal r) ≥ X ^ (1 - t) * Y ^ t :=
      le_trans h_am_gm h_final1
    have h_final : ∫⁻ z, h z ≥ X ^ (1 - t) * Y ^ t := by
      rw [h_layer_h]
      exact h_result
    exact h_final

/-! ### Unbounded 1D PL via truncation -/

/-- iSup of natural numbers in ENNReal is top. -/
lemma iSup_nat_eq_top : (⨆ N : ℕ, (N : ENNReal)) = ⊤ := by
  by_contra h
  have h' : (⨆ N : ℕ, (N : ENNReal)) ≠ ⊤ := h
  have h_lt : (⨆ N : ℕ, (N : ENNReal)) < ⊤ := lt_top_iff_ne_top.mpr h'
  obtain ⟨N, hN⟩ := exists_nat_ge (⨆ N : ℕ, (N : ENNReal)).toReal
  have h2 : (⨆ N : ℕ, (N : ENNReal)) ≤ (N : ENNReal) := by
    rw [← ENNReal.ofReal_toReal h']
    have hN' : (⨆ N : ℕ, (N : ENNReal)).toReal ≤ (N : ℝ) := hN
    have h21 : ENNReal.ofReal (⨆ N : ℕ, (N : ENNReal)).toReal ≤ ENNReal.ofReal (N : ℝ) :=
      ENNReal.ofReal_le_ofReal hN'
    have h22 : ENNReal.ofReal (N : ℝ) = (N : ENNReal) := by simp
    rw [h22] at h21
    exact h21
  have h3 : (↑(N + 1) : ENNReal) ≤ (⨆ i : ℕ, (i : ENNReal)) :=
    le_iSup (f := fun i : ℕ => (i : ENNReal)) (i := N + 1)
  have h4 : (↑(N + 1) : ENNReal) ≤ (N : ENNReal) := h3.trans h2
  have h_contra : ¬((↑(N + 1) : ENNReal) ≤ (N : ENNReal)) := by
    have h5 : (N : ENNReal) < (↑(N + 1) : ENNReal) := by exact_mod_cast Nat.lt_succ_self N
    exact not_le.mpr h5
  exact h_contra h4

/-- iSup of product of monotone ENNReal sequences. -/
lemma iSup_mul_eq {a b : ℕ → ENNReal} (ha_mono : Monotone a) (hb_mono : Monotone b) :
    (⨆ n, a n * b n) = (⨆ n, a n) * (⨆ n, b n) := by
  have h1 : (⨆ n, a n * b n) ≤ (⨆ n, a n) * (⨆ n, b n) := ENNReal.iSup_mul_le
  have h2 : (⨆ n, a n) * (⨆ n, b n) ≤ (⨆ n, a n * b n) := by
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro n
    rw [ENNReal.iSup_mul]
    apply iSup_le
    intro m
    have h3 : a m ≤ a (max m n) := ha_mono (le_max_left m n)
    have h4 : b n ≤ b (max m n) := hb_mono (le_max_right m n)
    have h5 : a m * b n ≤ a (max m n) * b (max m n) := mul_le_mul' h3 h4
    have h6 : a (max m n) * b (max m n) ≤ ⨆ (i : ℕ), a i * b i :=
      le_iSup (f := fun i : ℕ => a i * b i) (i := max m n)
    exact h5.trans h6
  exact le_antisymm h1 h2

/-- iSup of rpow of monotone ENNReal sequence. -/
lemma iSup_rpow_eq {a : ℕ → ENNReal} (ha_mono : Monotone a) {p : ℝ} (hp : 0 ≤ p) :
    (⨆ n, a n ^ p) = (⨆ n, a n) ^ p := by
  by_cases hp0 : p = 0
  · rw [hp0]; simp
  · have hp_pos : 0 < p := by exact lt_of_le_of_ne hp (Ne.symm hp0)
    have h_mono_f : Monotone (fun x : ENNReal => x ^ p) := fun x y h => ENNReal.rpow_le_rpow h hp
    have h_cont : Continuous (fun x : ENNReal => x ^ p) := ENNReal.continuous_rpow_const
    have h_bot : (0 : ENNReal) ^ p = 0 := ENNReal.zero_rpow_of_pos hp_pos
    exact (h_mono_f.map_iSup_of_continuousAt h_cont.continuousAt h_bot).symm

/-- **1D Prékopa–Leindler inequality** (unbounded).

For `0 < t < 1` and measurable `f, g, h : ℝ → ℝ≥0∞` satisfying
`h((1-t)x + ty) ≥ f(x)^(1-t) * g(y)^t` for all `x, y`, we have
`∫ h ≥ (∫ f)^(1-t) * (∫ g)^t`. -/
theorem prekopa_leindler_one_dim {f g h : ℝ → ENNReal}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {t : ℝ} (ht : 0 < t) (ht' : t < 1)
    (hcond : ∀ x y, h ((1 - t) * x + t * y) ≥ f x ^ (1 - t) * g y ^ t) :
    ∫⁻ x, h x ≥ (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t := by
  let fN : ℕ → ℝ → ENNReal := fun N x => f x ⊓ (N : ENNReal)
  let gN : ℕ → ℝ → ENNReal := fun N x => g x ⊓ (N : ENNReal)
  have hfN : ∀ N, Measurable (fN N) := fun N => hf.inf_const (N : ENNReal)
  have hgN : ∀ N, Measurable (gN N) := fun N => hg.inf_const (N : ENNReal)
  have h_mono_f : Monotone fN := by
    intro n m hnm x; have h : (n : ENNReal) ≤ (m : ENNReal) := by exact_mod_cast hnm
    exact inf_le_inf_left (f x) h
  have h_mono_g : Monotone gN := by
    intro n m hnm x; have h : (n : ENNReal) ≤ (m : ENNReal) := by exact_mod_cast hnm
    simpa [gN, inf_comm] using inf_le_inf_right (g x) h
  have h_pl_N : ∀ N, ∀ x y, h ((1 - t) * x + t * y) ≥ (fN N x) ^ (1 - t) * (gN N y) ^ t := by
    intro N x y
    have h1 : fN N x ≤ f x := inf_le_left
    have h2 : gN N y ≤ g y := inf_le_left
    have h3 : (fN N x) ^ (1 - t) ≤ (f x) ^ (1 - t) := ENNReal.rpow_le_rpow h1 (by linarith)
    have h4 : (gN N y) ^ t ≤ (g y) ^ t := ENNReal.rpow_le_rpow h2 (by linarith)
    have h_smul : (1 - t) • x + t • y = (1 - t) * x + t * y := by
      simp [smul_eq_mul]
    have h5 : h ((1 - t) * x + t * y) ≥ (f x) ^ (1 - t) * (g y) ^ t := by
      rw [←h_smul]
      exact hcond x y
    calc h ((1 - t) * x + t * y)
      ≥ (f x) ^ (1 - t) * (g y) ^ t := h5
    _ ≥ (fN N x) ^ (1 - t) * (gN N y) ^ t := mul_le_mul' h3 h4
  have h_main_N : ∀ N, ∫⁻ x, h x ≥ (∫⁻ x, fN N x) ^ (1 - t) * (∫⁻ x, gN N x) ^ t := by
    intro N
    have hM : ∀ x, fN N x ≤ (N : ENNReal) := fun x => inf_le_right
    have hN : ∀ x, gN N x ≤ (N : ENNReal) := fun x => inf_le_right
    exact prekopa_leindler_one_dim_bounded (f := fN N) (g := gN N) (h := h)
      (hfN N) (hgN N) hh ht ht' (h_pl_N N)
      (M_bound := (N : ENNReal)) (N_bound := (N : ENNReal))
      (hM_bound := hM) (hN_bound := hN)
      (hM_top := by simp) (hN_top := by simp)
  let I_f : ℕ → ENNReal := fun N => ∫⁻ x, fN N x
  let I_g : ℕ → ENNReal := fun N => ∫⁻ x, gN N x
  have h_mono_If : Monotone I_f := fun n m hnm => lintegral_mono (h_mono_f hnm)
  have h_mono_Ig : Monotone I_g := fun n m hnm => lintegral_mono (h_mono_g hnm)
  have h6 : ∀ N, ∫⁻ x, h x ≥ (I_f N) ^ (1 - t) * (I_g N) ^ t := h_main_N
  have h7 : (⨆ N, (I_f N) ^ (1 - t) * (I_g N) ^ t) ≤ ∫⁻ x, h x := iSup_le h6
  have h8 : (⨆ N, (I_f N) ^ (1 - t) * (I_g N) ^ t) =
      (⨆ N, (I_f N) ^ (1 - t)) * (⨆ N, (I_g N) ^ t) :=
    iSup_mul_eq (Monotone.comp (fun x y h => ENNReal.rpow_le_rpow h (by linarith)) h_mono_If)
      (Monotone.comp (fun x y h => ENNReal.rpow_le_rpow h (by linarith)) h_mono_Ig)
  have h9 : (⨆ N, (I_f N) ^ (1 - t)) = (⨆ N, I_f N) ^ (1 - t) :=
    iSup_rpow_eq h_mono_If (by linarith)
  have h10 : (⨆ N, (I_g N) ^ t) = (⨆ N, I_g N) ^ t :=
    iSup_rpow_eq h_mono_Ig (by linarith)
  have hIf : (⨆ N, I_f N) = ∫⁻ x, f x := by
    rw [← lintegral_iSup hfN h_mono_f]
    congr with x
    by_cases htop : f x = ⊤
    · have h4 : ∀ N : ℕ, fN N x = (N : ENNReal) := by
        intro N; simp [fN, htop]
      rw [htop]
      have h5 : (⨆ N : ℕ, fN N x) = (⨆ N : ℕ, (N : ENNReal)) := by
        congr with N; exact h4 N
      rw [h5, iSup_nat_eq_top]
    · have hfin : f x ≠ ⊤ := htop
      obtain ⟨N, hN⟩ := exists_nat_ge (f x).toReal
      have h2 : f x ≤ (N : ENNReal) := by
        rw [← ENNReal.ofReal_toReal hfin]
        have h21 : ENNReal.ofReal (f x).toReal ≤ ENNReal.ofReal (N : ℝ) := ENNReal.ofReal_le_ofReal hN
        have h22 : ENNReal.ofReal (N : ℝ) = (N : ENNReal) := by simp
        rw [h22] at h21
        exact h21
      have h3 : ∀ M ≥ N, fN M x = f x := by
        intro M hM
        have h4 : (M : ENNReal) ≥ f x := h2.trans (by exact_mod_cast hM)
        simp [fN, h4, inf_eq_left]
      apply le_antisymm
      · exact iSup_le (fun k => inf_le_left)
      · have h5 : fN N x ≤ (⨆ k, fN k x) := le_iSup (f := fun k => fN k x) (i := N)
        rw [h3 N (by linarith)] at h5
        exact h5
  have hIg : (⨆ N, I_g N) = ∫⁻ y, g y := by
    rw [← lintegral_iSup hgN h_mono_g]
    congr with y
    by_cases htop : g y = ⊤
    · have h4 : ∀ N : ℕ, gN N y = (N : ENNReal) := by
        intro N; simp [gN, htop]
      rw [htop]
      have h5 : (⨆ N : ℕ, gN N y) = (⨆ N : ℕ, (N : ENNReal)) := by
        congr with N; exact h4 N
      rw [h5, iSup_nat_eq_top]
    · have hfin : g y ≠ ⊤ := htop
      obtain ⟨N, hN⟩ := exists_nat_ge (g y).toReal
      have h2 : g y ≤ (N : ENNReal) := by
        rw [← ENNReal.ofReal_toReal hfin]
        have h21 : ENNReal.ofReal (g y).toReal ≤ ENNReal.ofReal (N : ℝ) := ENNReal.ofReal_le_ofReal hN
        have h22 : ENNReal.ofReal (N : ℝ) = (N : ENNReal) := by simp
        rw [h22] at h21
        exact h21
      have h3 : ∀ M ≥ N, gN M y = g y := by
        intro M hM
        have h4 : (M : ENNReal) ≥ g y := h2.trans (by exact_mod_cast hM)
        simp [gN, h4, inf_eq_left]
      apply le_antisymm
      · exact iSup_le (fun k => inf_le_left)
      · have h5 : gN N y ≤ (⨆ k, gN k y) := le_iSup (f := fun k => gN k y) (i := N)
        rw [h3 N (by linarith)] at h5
        exact h5
  calc (∫⁻ x, f x) ^ (1 - t) * (∫⁻ y, g y) ^ t
    = (⨆ N, I_f N) ^ (1 - t) * (⨆ N, I_g N) ^ t := by rw [hIf, hIg]
  _ = (⨆ N, (I_f N) ^ (1 - t)) * (⨆ N, (I_g N) ^ t) := by rw [h9, h10]
  _ = ⨆ N, (I_f N) ^ (1 - t) * (I_g N) ^ t := h8.symm
  _ ≤ ∫⁻ x, h x := h7

end Geometry
