import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.MollificationGradientBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.Perimeter

variable {n : ℕ} [Nonempty (Fin n)]

/-- Change of variables over a compact set: `∫_K f(x+w) = ∫_{K+w} f(y)`. -/
lemma integral_translation_compact
    {f : E n → ℝ} {K : Set (E n)} (hK : IsCompact K) {w : E n}
    (hf : IntegrableOn f (translateSet K w) volume) :
    ∫ x in K, f (x + w) = ∫ y in translateSet K w, f y := by
  let g : E n → E n := fun x => x + w
  have h_g_image : g '' K = translateSet K w := by
    ext y
    simp [g, translateSet, Set.mem_image]
    <;> constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, by abel⟩
  let f_ind : E n → ℝ := Set.indicator (g '' K) f
  have hK_meas : MeasurableSet K := hK.measurableSet
  have h_image_meas : MeasurableSet (g '' K) := (hK.image (by fun_prop)).measurableSet
  have h_f_integrable : Integrable f_ind volume := by
    have h1 : f_ind = Set.indicator (g '' K) f := by rfl
    rw [h1]
    have h2 : IntegrableOn f (g '' K) volume := by
      rw [h_g_image] at *; exact hf
    exact (integrable_indicator_iff h_image_meas).mpr h2
  have hmp : MeasurePreserving g volume volume := measurePreserving_add_right volume w
  have hme : MeasurableEmbedding g := measurableEmbedding_addRight w
  have h_eq1 : ∫ x, f_ind (g x) = ∫ y, f_ind y :=
    hmp.integral_comp hme f_ind
  have h_preimage : g ⁻¹' (g '' K) = K := by
    ext z
    simp [g, Set.mem_preimage, Set.mem_image]
    <;> constructor <;> rintro ⟨y, hy, h_eq⟩ <;> refine ⟨y, hy, by simpa [g] using h_eq⟩
  have h_eq2 : ∀ x, f_ind (g x) = Set.indicator K (f ∘ g) x := by
    intro x
    have h : f_ind (g x) = Set.indicator (g ⁻¹' (g '' K)) (f ∘ g) x := by
      simp [f_ind, Set.indicator_apply]
      <;> rfl
    rw [h, h_preimage]
  have h_main1 : ∫ x in K, f (g x) = ∫ x, f_ind (g x) := by
    have h_iff : ∫ x in K, f (g x) = ∫ x, Set.indicator K (f ∘ g) x := by
      rw [integral_indicator hK_meas] <;> rfl
    rw [h_iff]
    have h7 : Set.indicator K (f ∘ g) = fun x => f_ind (g x) := by
      funext x
      exact (h_eq2 x).symm
    rw [h7]
  have h_main2 : ∫ y, f_ind y = ∫ y in g '' K, f y := by
    have h : ∫ y, f_ind y = ∫ y, Set.indicator (g '' K) f y := by rfl
    rw [h, integral_indicator h_image_meas] <;> rfl
  calc
    ∫ x in K, f (x + w) = ∫ x in K, f (g x) := by rfl
    _ = ∫ x, f_ind (g x) := h_main1
    _ = ∫ y, f_ind y := h_eq1
    _ = ∫ y in g '' K, f y := h_main2
    _ = ∫ y in translateSet K w, f y := by rw [h_g_image]

/-- For a C¹ function `u`, the L¹ translation difference over compact `K`
is bounded by `‖v‖` times the L¹ norm of the gradient over the swept set. -/
lemma smooth_translation_integral_bound
    {u : E n → ℝ} (hu : ContDiff ℝ 1 u)
    {K : Set (E n)} (hK : IsCompact K)
    {v : E n} :
    ∫ x in K, |u (x + v) - u x| ≤
      ‖v‖ * ∫ x in (fun p : E n × ℝ => p.1 + p.2 • v) '' (K ×ˢ Set.Icc (0 : ℝ) 1),
        ‖fderiv ℝ u x‖ := by
  let K_v := (fun p : E n × ℝ => p.1 + p.2 • v) '' (K ×ˢ Set.Icc (0 : ℝ) 1)
  have hKv_compact : IsCompact K_v := (hK.prod isCompact_Icc).image (by fun_prop)
  have hKv_meas : MeasurableSet K_v := hKv_compact.measurableSet
  have hK_meas : MeasurableSet K := hK.measurableSet
  -- Empty K case
  by_cases hK_empty : K = ∅
  · rw [hK_empty]
    simp
  have h_diff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have h_cf_norm : Continuous (fun y : E n => ‖fderiv ℝ u y‖) :=
    (hu.continuous_fderiv (by norm_num)).norm
  let F : E n × ℝ → ℝ := fun p => ‖fderiv ℝ u (p.1 + p.2 • v)‖
  have hF_cont : Continuous F := by fun_prop
  let μ := volume.restrict K
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hμ_fin : volume K < ⊤ := hK.measure_lt_top
  have hν_fin : volume (Set.Icc (0 : ℝ) 1) < ⊤ := isCompact_Icc.measure_lt_top
  haveI hμ_finite : IsFiniteMeasure μ := by
    refine' ⟨_⟩
    have h : μ Set.univ = volume K := by
      simp [μ, Measure.restrict_apply, hK_meas] <;> rfl
    rw [h] <;> exact hμ_fin
  haveI hν_finite : IsFiniteMeasure ν := by
    refine' ⟨_⟩
    have h : ν Set.univ = volume (Set.Icc (0 : ℝ) 1) := by
      simp [ν, Measure.restrict_apply, isCompact_Icc.measurableSet] <;> rfl
    rw [h] <;> exact hν_fin
  have h_prod_restrict : μ.prod ν = (volume.prod volume).restrict (K ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [Measure.prod_restrict] <;> simp [μ, ν]
  have hF_int : Integrable F (μ.prod ν) := by
    rw [h_prod_restrict]
    exact hF_cont.locallyIntegrable.integrableOn_isCompact (hK.prod isCompact_Icc)
  -- FTC for each x
  have h_ftc : ∀ (x : E n), u (x + v) - u x =
      ∫ t in Set.Icc (0 : ℝ) 1, fderiv ℝ u (x + t • v) v := by
    intro x
    let g : ℝ → ℝ := fun t => u (x + t • v)
    have hg_diff : ∀ (t : ℝ), t ∈ Set.uIcc (0 : ℝ) 1 →
        HasDerivAt g (fderiv ℝ u (x + t • v) v) t := by
      intro t _
      have h1 : HasFDerivAt u (fderiv ℝ u (x + t • v)) (x + t • v) :=
        h_diff.differentiableAt.hasFDerivAt
      have h21 : HasDerivAt (fun t : ℝ => t • v) v t := by
        have h_id : HasDerivAt (fun t : ℝ => t) (1 : ℝ) t := hasDerivAt_id t
        have h : HasDerivAt (fun t : ℝ => t • v) ((1 : ℝ) • v) t := h_id.smul_const v
        have h_simp : (1 : ℝ) • v = v := by simp
        rw [h_simp] at h; exact h
      have h22 : HasDerivAt (fun t : ℝ => x) (0 : E n) t := hasDerivAt_const t x
      have h2 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
        have h_sum : HasDerivAt (fun t : ℝ => x + t • v) ((0 : E n) + v) t := h22.add h21
        simpa using h_sum
      exact h1.comp_hasDerivAt t h2
    have h_cont : Continuous (fun t : ℝ => fderiv ℝ u (x + t • v) v) := by fun_prop
    have h_int : IntervalIntegrable (fun t : ℝ => fderiv ℝ u (x + t • v) v) volume 0 1 :=
      h_cont.intervalIntegrable 0 1
    have h_eq1 : ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • v) v = g 1 - g 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hg_diff h_int
    have h_eq2 : ∫ t in (0 : ℝ)..1, fderiv ℝ u (x + t • v) v =
        ∫ t in Set.Icc (0 : ℝ) 1, fderiv ℝ u (x + t • v) v := by
      let f_t : ℝ → ℝ := fun t => fderiv ℝ u (x + t • v) v
      have h_eq_Ioc : ∫ t in (0 : ℝ)..1, f_t t = ∫ t in Set.Ioc (0 : ℝ) 1, f_t t :=
        intervalIntegral.integral_of_le (by norm_num)
      have h_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
        have h_null : volume ({0} : Set ℝ) = 0 := by simp
        exact Measure.ae_ne volume 0
      have h_ae : ∀ᵐ t : ℝ, Set.indicator (Set.Ioc (0 : ℝ) 1) f_t t = Set.indicator (Set.Icc (0 : ℝ) 1) f_t t := by
        filter_upwards [h_ne_zero] with t ht
        by_cases h : t ∈ Set.Ioc (0 : ℝ) 1
        · have h2 : t ∈ Set.Icc (0 : ℝ) 1 := by
            simp only [Set.mem_Ioc, Set.mem_Icc] at h ⊢ <;> exact ⟨by linarith, h.2⟩
          simp [Set.indicator_apply, h, h2]
        · have h2 : t ∉ Set.Icc (0 : ℝ) 1 := by
            intro h3
            have h4 : 0 ≤ t := h3.1
            have h5 : 0 < t := lt_of_le_of_ne h4 (Ne.symm ht)
            exact h ⟨h5, h3.2⟩
          simp [Set.indicator_apply, h, h2]
      have h_eq_Ioc_Icc : ∫ t, Set.indicator (Set.Ioc (0 : ℝ) 1) f_t t = ∫ t, Set.indicator (Set.Icc (0 : ℝ) 1) f_t t :=
        integral_congr_ae h_ae
      have h_final : ∫ t in Set.Ioc (0 : ℝ) 1, f_t t = ∫ t in Set.Icc (0 : ℝ) 1, f_t t := by
        simpa [integral_indicator] using h_eq_Ioc_Icc
      rw [h_eq_Ioc, h_final]
    simpa [g] using h_eq1.symm.trans h_eq2
  -- Pointwise absolute bound
  have h_pointwise : ∀ (x : E n), |u (x + v) - u x| ≤ ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) := by
    intro x
    rw [h_ftc x]
    have h_abs_int : Integrable (fun t : ℝ => fderiv ℝ u (x + t • v) v) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      have h_cont : Continuous (fun t : ℝ => fderiv ℝ u (x + t • v) v) := by fun_prop
      exact h_cont.locallyIntegrable.integrableOn_isCompact isCompact_Icc
    have h3 : |∫ t in Set.Icc (0 : ℝ) 1, fderiv ℝ u (x + t • v) v| ≤
        ∫ t in Set.Icc (0 : ℝ) 1, |fderiv ℝ u (x + t • v) v| := abs_integral_le_integral_abs
    have h4 : ∀ (t : ℝ), |fderiv ℝ u (x + t • v) v| ≤ F (x, t) * ‖v‖ := by
      intro t; exact (fderiv ℝ u (x + t • v)).le_opNorm v
    have h_abs2 : Integrable (fun t : ℝ => |fderiv ℝ u (x + t • v) v|) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      h_abs_int.norm
    have h_prod : Integrable (fun t : ℝ => F (x, t) * ‖v‖) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      have h_cont : Continuous (fun t : ℝ => F (x, t)) := by fun_prop
      exact h_cont.locallyIntegrable.integrableOn_isCompact isCompact_Icc |>.mul_const ‖v‖
    have h5 : ∫ t in Set.Icc (0 : ℝ) 1, |fderiv ℝ u (x + t • v) v| ≤
        ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) * ‖v‖ := by
      apply integral_mono_ae h_abs2 h_prod
      filter_upwards with t; exact h4 t
    have h6 : ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) * ‖v‖ = ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) := by
      have h_comm : (fun t : ℝ => F (x, t) * ‖v‖) = fun t : ℝ => ‖v‖ * F (x, t) := by funext t; ring
      rw [h_comm, integral_const_mul]
    calc
      |∫ t in Set.Icc (0 : ℝ) 1, fderiv ℝ u (x + t • v) v|
        ≤ ∫ t in Set.Icc (0 : ℝ) 1, |fderiv ℝ u (x + t • v) v| := h3
      _ ≤ ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) * ‖v‖ := h5
      _ = ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) := h6
  -- Integrability from Fubini
  have h_marginal_x : Integrable (fun x : E n => ∫ t : ℝ, F (x, t) ∂ν) μ :=
    hF_int.integral_prod_left
  have h_marginal_t : Integrable (fun t : ℝ => ∫ x : E n, F (x, t) ∂μ) ν :=
    hF_int.integral_prod_right
  have h_ion_lhs : IntegrableOn (fun x : E n => |u (x + v) - u x|) K volume := by
    have h_cont : Continuous (fun x : E n => |u (x + v) - u x|) := by fun_prop
    exact h_cont.locallyIntegrable.integrableOn_isCompact hK
  have h_ion_rhs : IntegrableOn (fun x : E n => ∫ t in Set.Icc (0 : ℝ) 1, F (x, t)) K volume := by
    have h_eq : (fun x : E n => ∫ t in Set.Icc (0 : ℝ) 1, F (x, t)) =
        (fun x : E n => ∫ t : ℝ, F (x, t) ∂ν) := by funext x; rfl
    rw [h_eq]
    exact h_marginal_x
  have h_ion_rhs_v : IntegrableOn (fun x : E n => ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, F (x, t)) K volume := by
    have h_eq : (fun x : E n => ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, F (x, t)) =
        (fun x : E n => (∫ t in Set.Icc (0 : ℝ) 1, F (x, t)) * ‖v‖) := by funext x; ring
    rw [h_eq]
    exact h_ion_rhs.mul_const ‖v‖
  have h5 : ∫ x in K, |u (x + v) - u x| ≤ ∫ x in K, ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) := by
    apply integral_mono_ae h_ion_lhs h_ion_rhs_v
    filter_upwards with x; exact h_pointwise x
  have h6 : ∫ x in K, ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) =
      ‖v‖ * ∫ x in K, ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) := by
    rw [integral_const_mul]
  rw [h6] at h5
  -- Fubini
  have h_fub : ∫ x in K, ∫ t in Set.Icc (0 : ℝ) 1, F (x, t) =
      ∫ t in Set.Icc (0 : ℝ) 1, ∫ x in K, F (x, t) := by
    have h1 : ∫ x, ∫ t, F (x, t) ∂ν ∂μ = ∫ z, F z ∂(μ.prod ν) :=
      (MeasureTheory.integral_prod F hF_int).symm
    have h2 : ∫ z, F z ∂(μ.prod ν) = ∫ t, ∫ x, F (x, t) ∂μ ∂ν :=
      MeasureTheory.integral_prod_symm F hF_int
    have h3 : ∫ x, ∫ t, F (x, t) ∂ν ∂μ = ∫ t, ∫ x, F (x, t) ∂μ ∂ν := by rw [h1, h2]
    simpa [μ, ν] using h3
  rw [h_fub] at h5
  -- For each t: change variables and bound by K_v
  have h7 : ∀ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
      ∫ x in K, F (x, t) ≤ ∫ y in K_v, ‖fderiv ℝ u y‖ := by
    intro t ht
    let A := translateSet K (t • v)
    let f_y : E n → ℝ := fun y => ‖fderiv ℝ u y‖
    have hA_meas : MeasurableSet A := (hK.image (by fun_prop)).measurableSet
    have h_trans : ∫ x in K, F (x, t) = ∫ y in A, f_y y := by
      have h_ion : IntegrableOn f_y A volume :=
        h_cf_norm.locallyIntegrable.integrableOn_isCompact (hK.image (by fun_prop))
      exact integral_translation_compact hK h_ion
    rw [h_trans]
    have h_sub : A ⊆ K_v := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact ⟨(x, t), ⟨hx, ht⟩, by simp [A, translateSet] <;> abel⟩
    have h_ion_Kv : IntegrableOn f_y K_v volume :=
      h_cf_norm.locallyIntegrable.integrableOn_isCompact hKv_compact
    have h_ion_A : IntegrableOn f_y A volume := h_ion_Kv.mono_set h_sub
    have h_nonneg : ∀ y, 0 ≤ f_y y := fun y => norm_nonneg _
    -- Indicator monotonicity: indicator A f ≤ indicator K_v f
    have h_ind_mono : ∀ y, Set.indicator A f_y y ≤ Set.indicator K_v f_y y := by
      intro y
      by_cases h : y ∈ A
      · have h2 : y ∈ K_v := h_sub h
        simp [Set.indicator_apply, h, h2]
      · have h3 : Set.indicator A f_y y = 0 := by
          simp [Set.indicator_apply, h]
        rw [h3]
        have h4 : 0 ≤ Set.indicator K_v f_y y := by
          apply Set.indicator_nonneg
          intro z _; exact norm_nonneg _
        exact h4
    have h1 : ∫ y, Set.indicator A f_y y ≤ ∫ y, Set.indicator K_v f_y y :=
      integral_mono_ae (h_ion_A.integrable_indicator hA_meas)
        (h_ion_Kv.integrable_indicator hKv_meas) (by filter_upwards with y; exact h_ind_mono y)
    have hA_int : ∫ y in A, f_y y = ∫ y, Set.indicator A f_y y := by
      rw [integral_indicator hA_meas] <;> rfl
    have hKv_int : ∫ y in K_v, f_y y = ∫ y, Set.indicator K_v f_y y := by
      rw [integral_indicator hKv_meas] <;> rfl
    rw [hA_int, hKv_int]
    exact h1
  -- Integrability of G(t) from Fubini
  have h_int_G : IntegrableOn (fun t : ℝ => ∫ x in K, F (x, t)) (Set.Icc (0 : ℝ) 1) volume := by
    have h_eq : (fun t : ℝ => ∫ x in K, F (x, t)) =
        (fun t : ℝ => ∫ x : E n, F (x, t) ∂μ) := by funext t; rfl
    rw [h_eq]
    exact h_marginal_t
  have h_int_const : IntegrableOn (fun t : ℝ => ∫ y in K_v, ‖fderiv ℝ u y‖) (Set.Icc (0 : ℝ) 1) volume :=
    continuous_const.locallyIntegrable.integrableOn_isCompact isCompact_Icc
  have h8 : ∫ t in Set.Icc (0 : ℝ) 1, (∫ x in K, F (x, t)) ≤
      ∫ t in Set.Icc (0 : ℝ) 1, ∫ y in K_v, ‖fderiv ℝ u y‖ := by
    apply integral_mono_ae h_int_G h_int_const
    filter_upwards [ae_restrict_mem isCompact_Icc.measurableSet] with t ht
    exact h7 t ht
  have h9 : ∫ t in Set.Icc (0 : ℝ) 1, ∫ y in K_v, ‖fderiv ℝ u y‖ = ∫ y in K_v, ‖fderiv ℝ u y‖ := by
    simp [integral_const, Real.volume_Icc] <;> norm_num
  have h10 : ‖v‖ * ∫ t in Set.Icc (0 : ℝ) 1, (∫ x in K, F (x, t)) ≤ ‖v‖ * ∫ y in K_v, ‖fderiv ℝ u y‖ := by
    have h11 : ∫ t in Set.Icc (0 : ℝ) 1, (∫ x in K, F (x, t)) ≤ ∫ y in K_v, ‖fderiv ℝ u y‖ :=
      h8.trans (le_of_eq h9)
    exact mul_le_mul_of_nonneg_left h11 (by positivity)
  exact le_trans h5 h10

/-- **Local translation bound (forward difference).**

With `K + [0,1]·v ⊆ Ω`, the symmetric difference between `S` and `S-v`
inside `K` is bounded by `n·‖v‖·P(S;Ω)`. -/
lemma local_translation_bound
    {S : Set (E n)} (hS : MeasurableSet S)
    {Ω : Set (E n)} (hΩ_open : IsOpen Ω)
    {K : Set (E n)} (hK_compact : IsCompact K) (hK_sub : K ⊆ Ω)
    {v : E n} (hv_small : ∀ t ∈ Set.Icc (0 : ℝ) 1, translateSet K (t • v) ⊆ Ω) :
    volume ((symmDiff S (translateSet S (-v))) ∩ K) ≤
      (n : ENNReal) * ENNReal.ofReal ‖v‖ * perimeterIn S Ω := by
  by_cases hv : v = 0
  · subst hv; simp [translateSet, symmDiff_self] <;> exact zero_le _
  by_cases hP : perimeterIn S Ω = ⊤
  · rw [hP]
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h_n_pos : 0 < n := Fin.pos_iff_nonempty.mpr ‹Nonempty (Fin n)›
    have h_n_ne_zero : (n : ENNReal) ≠ 0 := by exact_mod_cast h_n_pos.ne'
    have h_ne_zero : (n : ENNReal) * ENNReal.ofReal ‖v‖ ≠ 0 :=
      mul_ne_zero h_n_ne_zero (ENNReal.ofReal_pos.mpr hpos).ne'
    rw [ENNReal.mul_top h_ne_zero] <;> exact le_top
  have hP_lt : perimeterIn S Ω < ⊤ := lt_top_iff_ne_top.mpr hP
  have hP_fin : (n : ENNReal) * perimeterIn S Ω < ⊤ := ENNReal.mul_lt_top (by simp) hP_lt
  let K_v : Set (E n) := (fun p : E n × ℝ => p.1 + p.2 • v) '' (K ×ˢ Set.Icc (0 : ℝ) 1)
  have hKv_compact : IsCompact K_v := (hK_compact.prod isCompact_Icc).image (by fun_prop)
  have hKv_sub : K_v ⊆ Ω := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have h3 : p.1 + p.2 • v ∈ translateSet K (p.2 • v) := ⟨p.1, hp.1, by abel_nf⟩
    exact hv_small p.2 hp.2 h3
  rcases mollification_gradient_bound hS hΩ_open hKv_compact hKv_sub with
    ⟨u, N, _h_u_eq, h_u_smooth, h_u_bound, h_u_l1, h_u_grad⟩
  let χ : E n → ℝ := Set.indicator S (fun _ => (1 : ℝ))
  let S' : Set (E n) := translateSet S (-v)
  have hS'_meas : MeasurableSet S' := by
    have h_cont : Continuous (fun x : E n => x + v) := by fun_prop
    have h_eq : S' = (fun x : E n => x + v) ⁻¹' S := by
      ext x
      simp only [S', translateSet, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, h_eq2⟩
        have h : y - v = x := h_eq2
        have h' : y = x + v := by rw [← h]; simp
        rw [h'] at hy; exact hy
      · intro hx
        refine ⟨x + v, hx, ?_⟩
        simp
    rw [h_eq]
    exact h_cont.measurable hS
  let χ' : E n → ℝ := Set.indicator S' (fun _ => (1 : ℝ))
  have h_chi'_eq : ∀ x, χ' x = χ (x + v) := by
    intro x
    have h1 : x ∈ S' ↔ x + v ∈ S := by
      simp only [S', translateSet, Set.mem_image]
      constructor
      · rintro ⟨y, hy, h_eq2⟩
        have h : y - v = x := h_eq2
        have h' : y = x + v := by rw [← h]; simp
        rw [h'] at hy; exact hy
      · intro hx
        exact ⟨x + v, hx, by simp⟩
    have h2 : χ' x = Set.indicator S' (fun _ => (1 : ℝ)) x := by rfl
    rw [h2]
    by_cases h : x ∈ S'
    · have h3 : x + v ∈ S := h1.mp h
      have h4 : Set.indicator S' (fun _ => (1 : ℝ)) x = 1 := by
        simp [Set.indicator_apply, h]
      have h5 : χ (x + v) = 1 := by
        simp [χ, Set.indicator_apply, h3]
      rw [h4, h5]
    · have h3 : x + v ∉ S := by tauto
      have h4 : Set.indicator S' (fun _ => (1 : ℝ)) x = 0 := by
        simp [Set.indicator_apply, h]
      have h5 : χ (x + v) = 0 := by
        simp [χ, Set.indicator_apply, h3]
      rw [h4, h5]
  let DSet : Set (E n) := (symmDiff S S') ∩ K
  have hSD_meas : MeasurableSet (symmDiff S S') :=
    (hS.diff hS'_meas).union (hS'_meas.diff hS)
  have hD_meas : MeasurableSet DSet := hSD_meas.inter hK_compact.measurableSet
  have h_sub : DSet ⊆ K := Set.inter_subset_right
  have hD_fin : volume DSet < ⊤ := lt_of_le_of_lt (measure_mono h_sub) hK_compact.measure_lt_top
  have h1 : ∀ x, |χ' x - χ x| = Set.indicator (symmDiff S S') (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases h : x ∈ symmDiff S S'
    · have h_ind : Set.indicator (symmDiff S S') (fun _ => (1 : ℝ)) x = 1 := by
        simp [Set.indicator_apply, h] <;> norm_num
      rw [h_ind]
      rcases h with (h | h) <;> simp [χ, χ', h.1, h.2] <;> norm_num
    · have h_ind : Set.indicator (symmDiff S S') (fun _ => (1 : ℝ)) x = 0 := by
        simp [Set.indicator_apply, h] <;> norm_num
      rw [h_ind]
      have h_eq : χ' x = χ x := by
        simp only [Set.mem_symmDiff] at h
        by_cases hSx : x ∈ S <;> by_cases hS'x : x ∈ S' <;> simp [χ, χ', hSx, hS'x] at h ⊢ <;> tauto
      rw [h_eq] <;> simp
  have h4 : Set.indicator K (Set.indicator (symmDiff S S') (fun _ => (1 : ℝ))) =
      Set.indicator DSet (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hK : x ∈ K
    · by_cases hA : x ∈ symmDiff S S'
      · have hD : x ∈ DSet := ⟨hA, hK⟩
        simp [Set.indicator_apply, hK, hA, hD]
      · have hD : x ∉ DSet := by intro h; exact hA h.1
        simp [Set.indicator_apply, hK, hA, hD]
    · have hD : x ∉ DSet := by intro h; exact hK h.2
      simp [Set.indicator_apply, hK, hD]
  have h_int_vol : ∫ x in K, |χ' x - χ x| = (volume DSet).toReal := by
    have h2 : ∫ x in K, |χ' x - χ x| = ∫ x in K, Set.indicator (symmDiff S S') (fun _ => (1 : ℝ)) x := by
      congr with x; exact h1 x
    rw [h2]
    have h3 : ∫ x in K, Set.indicator (symmDiff S S') (fun _ => (1 : ℝ)) x =
        ∫ x, Set.indicator K (Set.indicator (symmDiff S S') (fun _ => (1 : ℝ))) x := by
      rw [integral_indicator hK_compact.measurableSet] <;> rfl
    rw [h3, h4]
    have h5 : ∫ x, Set.indicator DSet (fun _ => (1 : ℝ)) x = ∫ x in DSet, (1 : ℝ) := by
      rw [integral_indicator hD_meas] <;> rfl
    rw [h5]; simp [integral_const, hD_fin.ne] <;> rfl
  let K_v_trans : Set (E n) := translateSet K v
  have hKvt_compact : IsCompact K_v_trans := hK_compact.image (by fun_prop)
  have h_l1_K : Filter.Tendsto (fun k => ∫ x in K, |u k x - χ x|) Filter.atTop (nhds 0) :=
    h_u_l1 K hK_compact
  have h_l1_Kvt : Filter.Tendsto (fun k => ∫ x in K_v_trans, |u k x - χ x|) Filter.atTop (nhds 0) :=
    h_u_l1 K_v_trans hKvt_compact
  have h_change_var : ∀ k, ∫ x in K, |u k (x + v) - χ' x| = ∫ y in K_v_trans, |u k y - χ y| := by
    intro k
    have h4 : ∀ x, |u k (x + v) - χ' x| = |u k (x + v) - χ (x + v)| := by
      intro x; rw [h_chi'_eq x]
    have h : ∫ x in K, |u k (x + v) - χ' x| = ∫ x in K, |u k (x + v) - χ (x + v)| := by
      congr with x; exact h4 x
    rw [h]
    have h_cont : Continuous (u k) := (h_u_smooth k).continuous
    have h_χ_meas : Measurable χ := measurable_const.indicator hS
    have h_bound : ∀ᵐ y ∂(volume.restrict K_v_trans), |u k y - χ y| ≤ 1 := by
      filter_upwards with y
      have h1 : 0 ≤ u k y ∧ u k y ≤ 1 := h_u_bound k y
      have h2 : χ y = 0 ∨ χ y = 1 := by
        by_cases h : y ∈ S <;> simp [χ, h] <;> norm_num
      rcases h2 with (h2 | h2)
      · rw [h2]
        have h3 : 0 ≤ u k y := h1.1
        have h4 : u k y ≤ 1 := h1.2
        have h5 : |u k y - 0| = u k y := by
          have h6 : u k y - 0 = u k y := by ring
          rw [h6, abs_of_nonneg h3]
        rw [h5]; exact h4
      · rw [h2]
        have h3 : -1 ≤ u k y - 1 := by linarith [h1.1]
        have h4 : u k y - 1 ≤ 0 := by linarith [h1.2]
        have h5 : |u k y - 1| = -(u k y - 1) := abs_of_nonpos h4
        rw [h5]; linarith
    have h_ae : AEStronglyMeasurable (fun y : E n => |u k y - χ y|) volume :=
      (h_cont.measurable.sub h_χ_meas).norm.aestronglyMeasurable
    have h_ion : IntegrableOn (fun y : E n => |u k y - χ y|) K_v_trans volume :=
      Measure.integrableOn_of_bounded hKvt_compact.measure_lt_top.ne h_ae
        (M := 1) (by filter_upwards [h_bound] with y hy; simpa [Real.norm_eq_abs] using hy)
    exact integral_translation_compact hK_compact h_ion
  have h_grad_bound : ∀ k ≥ N,
      ENNReal.ofReal (∫ x in K_v, ‖fderiv ℝ (u k) x‖) ≤ (n : ENNReal) * perimeterIn S Ω := by
    intro k hk
    have h1 : eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K_v) ≤
        (n : ENNReal) * perimeterIn S Ω := h_u_grad k hk
    have h2 : eLpNorm (fderiv ℝ (u k)) (1 : NNReal) (volume.restrict K_v) =
        ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖ ∂(volume.restrict K_v) := by
      simpa [eLpNorm_one_eq_lintegral_enorm] using rfl
    rw [h2] at h1
    let h_cf : Continuous (fun x : E n => ‖fderiv ℝ (u k) x‖) :=
      (h_u_smooth k).continuous_fderiv (by norm_num) |>.norm
    have h_local : LocallyIntegrable (fun x : E n => ‖fderiv ℝ (u k) x‖) volume := h_cf.locallyIntegrable
    have h_int : Integrable (fun x : E n => ‖fderiv ℝ (u k) x‖) (volume.restrict K_v) :=
      h_local.integrableOn_isCompact hKv_compact
    have h3 : ∫⁻ x, ENNReal.ofReal ‖fderiv ℝ (u k) x‖ ∂(volume.restrict K_v) =
        ENNReal.ofReal (∫ x in K_v, ‖fderiv ℝ (u k) x‖) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int (by filter_upwards with x; positivity)] <;> rfl
    rw [h3] at h1; exact h1
  have h_grad_real : ∀ k ≥ N, ∫ x in K_v, ‖fderiv ℝ (u k) x‖ ≤
      ((n : ENNReal) * perimeterIn S Ω).toReal := by
    intro k hk
    have h4 := h_grad_bound k hk
    have h5 : ((n : ENNReal) * perimeterIn S Ω) < ⊤ := hP_fin
    have h6 : ENNReal.ofReal (∫ x in K_v, ‖fderiv ℝ (u k) x‖) ≤
        ENNReal.ofReal (((n : ENNReal) * perimeterIn S Ω).toReal) := by
      rw [ENNReal.ofReal_toReal h5.ne] at *; exact h4
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h6
  have h_triangle : ∀ k, ∫ x in K, |χ' x - χ x| ≤
      (∫ x in K, |χ' x - u k (x + v)|) +
      (∫ x in K, |u k (x + v) - u k x|) +
      (∫ x in K, |u k x - χ x|) := by
    intro k
    have h3 : ∀ x, |χ' x - χ x| ≤
        |χ' x - u k (x + v)| + |u k (x + v) - u k x| + |u k x - χ x| := by
      intro x
      have h1 : |χ' x - χ x| ≤ |χ' x - u k (x + v)| + |u k (x + v) - χ x| := by
        calc |χ' x - χ x|
          = |(χ' x - u k (x + v)) + (u k (x + v) - χ x)| := by rw [sub_add_sub_cancel]
        _ ≤ |χ' x - u k (x + v)| + |u k (x + v) - χ x| := by exact abs_add_le (χ' x - u k (x + v)) (u k (x + v) - χ x)
      have h2 : |u k (x + v) - χ x| ≤ |u k (x + v) - u k x| + |u k x - χ x| := by
        calc |u k (x + v) - χ x|
          = |(u k (x + v) - u k x) + (u k x - χ x)| := by rw [sub_add_sub_cancel]
        _ ≤ |u k (x + v) - u k x| + |u k x - χ x| := by exact abs_add_le (u k (x + v) - u k x) (u k x - χ x)
      linarith
    have h_cont : Continuous (u k) := (h_u_smooth k).continuous
    have h_χ_meas : Measurable χ := measurable_const.indicator hS
    have h_χ'_meas : Measurable χ' := measurable_const.indicator hS'_meas
    have h_f1 : Continuous (fun x => u k (x + v)) := h_cont.comp (by fun_prop)
    have h_χ_bdd : ∀ x, |χ x| ≤ 1 := by
      intro x; by_cases h : x ∈ S <;> simp [χ, h] <;> norm_num
    have h_χ'_bdd : ∀ x, |χ' x| ≤ 1 := by
      intro x; by_cases h : x ∈ S' <;> simp [χ', h] <;> norm_num
    have h_u_bdd : ∀ x, |u k x| ≤ 1 := by
      intro x
      have h1 : 0 ≤ u k x := (h_u_bound k x).1
      have h2 : u k x ≤ 1 := (h_u_bound k x).2
      have h3 : |u k x| = u k x := abs_of_nonneg h1
      rw [h3]; exact h2
    have h_uv_bdd : ∀ x, |u k (x + v)| ≤ 1 := fun x => h_u_bdd (x + v)
    have h_ion1 : IntegrableOn (fun x => |χ' x - u k (x + v)|) K volume := by
      have h_meas : Measurable (fun x => |χ' x - u k (x + v)|) :=
        (h_χ'_meas.sub h_f1.measurable).norm
      have h_bdd : ∀ x, |χ' x - u k (x + v)| ≤ 2 := by
        intro x; have h1 : |χ' x| ≤ 1 := h_χ'_bdd x
        have h2 : |u k (x + v)| ≤ 1 := h_uv_bdd x
        calc |χ' x - u k (x + v)| ≤ |χ' x| + |u k (x + v)| := by exact abs_sub (χ' x) (u k (x + v))
          _ ≤ 2 := by linarith
      exact Measure.integrableOn_of_bounded hK_compact.measure_lt_top.ne
        h_meas.aestronglyMeasurable (M := 2) (by filter_upwards with x; simpa [Real.norm_eq_abs] using h_bdd x)
    have h_ion2 : IntegrableOn (fun x => |u k (x + v) - u k x|) K volume := by
      have h : Continuous (fun x => |u k (x + v) - u k x|) := (h_f1.sub h_cont).norm
      exact h.locallyIntegrable.integrableOn_isCompact hK_compact
    have h_ion3 : IntegrableOn (fun x => |u k x - χ x|) K volume := by
      have h_meas : Measurable (fun x => |u k x - χ x|) :=
        (h_cont.measurable.sub h_χ_meas).norm
      have h_bdd : ∀ x, |u k x - χ x| ≤ 2 := by
        intro x; have h1 : |u k x| ≤ 1 := h_u_bdd x
        have h2 : |χ x| ≤ 1 := h_χ_bdd x
        calc |u k x - χ x| ≤ |u k x| + |χ x| := by exact abs_sub (u k x) (χ x)
          _ ≤ 2 := by linarith
      exact Measure.integrableOn_of_bounded hK_compact.measure_lt_top.ne
        h_meas.aestronglyMeasurable (M := 2) (by filter_upwards with x; simpa [Real.norm_eq_abs] using h_bdd x)
    have h_ion_lhs : IntegrableOn (fun x => |χ' x - χ x|) K volume := by
      have h_meas : Measurable (fun x => |χ' x - χ x|) := (h_χ'_meas.sub h_χ_meas).norm
      have h_bdd : ∀ x, |χ' x - χ x| ≤ 1 := by
        intro x
        have h1 : χ' x = 0 ∨ χ' x = 1 := by
          by_cases h : x ∈ S' <;> simp [χ', h] <;> norm_num
        have h2 : χ x = 0 ∨ χ x = 1 := by
          by_cases h : x ∈ S <;> simp [χ, h] <;> norm_num
        rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> simp [h1, h2] <;> norm_num
      exact Measure.integrableOn_of_bounded hK_compact.measure_lt_top.ne
        h_meas.aestronglyMeasurable (M := 1) (by filter_upwards with x; simpa [Real.norm_eq_abs] using h_bdd x)
    have h_ion12 : IntegrableOn (fun x => |χ' x - u k (x + v)| + |u k (x + v) - u k x|) K volume :=
      h_ion1.add h_ion2
    have h_ion_sum : IntegrableOn (fun x =>
        (|χ' x - u k (x + v)| + |u k (x + v) - u k x|) + |u k x - χ x|) K volume :=
      h_ion12.add h_ion3
    have h_ineq : ∫ x in K, |χ' x - χ x| ≤
        ∫ x in K, (|χ' x - u k (x + v)| + |u k (x + v) - u k x|) + |u k x - χ x| :=
      integral_mono_ae h_ion_lhs h_ion_sum (by filter_upwards with x; exact h3 x)
    have h_sum_eq : ∫ x in K, (|χ' x - u k (x + v)| + |u k (x + v) - u k x|) + |u k x - χ x| =
        (∫ x in K, |χ' x - u k (x + v)|) + (∫ x in K, |u k (x + v) - u k x|) + (∫ x in K, |u k x - χ x|) := by
      rw [integral_add h_ion12 h_ion3, integral_add h_ion1 h_ion2] <;> ring
    rw [h_sum_eq] at h_ineq
    exact h_ineq
  have h_smooth_bound : ∀ k, ∫ x in K, |u k (x + v) - u k x| ≤
      ‖v‖ * ∫ x in K_v, ‖fderiv ℝ (u k) x‖ :=
    fun k => smooth_translation_integral_bound (h_u_smooth k) hK_compact
  have h_main_bound : ∀ k ≥ N, ∫ x in K, |χ' x - χ x| ≤
      (∫ x in K_v_trans, |u k x - χ x|) +
      ‖v‖ * ((n : ENNReal) * perimeterIn S Ω).toReal +
      (∫ x in K, |u k x - χ x|) := by
    intro k hk
    have h6 := h_triangle k
    have h7 : ∫ x in K, |χ' x - u k (x + v)| = ∫ x in K_v_trans, |u k x - χ x| := by
      have h_abs : ∀ x, |χ' x - u k (x + v)| = |u k (x + v) - χ' x| := by
        intro x; rw [abs_sub_comm]
      have h_eq : ∫ x in K, |χ' x - u k (x + v)| = ∫ x in K, |u k (x + v) - χ' x| := by
        congr with x; exact h_abs x
      rw [h_eq]; exact h_change_var k
    have h8 : ∫ x in K, |u k (x + v) - u k x| ≤ ‖v‖ * ∫ x in K_v, ‖fderiv ℝ (u k) x‖ :=
      h_smooth_bound k
    have h9 : ∫ x in K_v, ‖fderiv ℝ (u k) x‖ ≤ ((n : ENNReal) * perimeterIn S Ω).toReal :=
      h_grad_real k hk
    have h10 : ∫ x in K, |χ' x - χ x| ≤
        (∫ x in K_v_trans, |u k x - χ x|) +
        (∫ x in K, |u k (x + v) - u k x|) +
        (∫ x in K, |u k x - χ x|) := by
      have h6' := h6
      rw [h7] at h6'
      exact h6'
    have h11 : (∫ x in K, |u k (x + v) - u k x|) ≤
        ‖v‖ * ((n : ENNReal) * perimeterIn S Ω).toReal := by
      calc
        (∫ x in K, |u k (x + v) - u k x|)
          ≤ ‖v‖ * ∫ x in K_v, ‖fderiv ℝ (u k) x‖ := h8
        _ ≤ ‖v‖ * ((n : ENNReal) * perimeterIn S Ω).toReal := by gcongr
    linarith
  let C : ℝ := ‖v‖ * ((n : ENNReal) * perimeterIn S Ω).toReal
  have hC_nonneg : 0 ≤ C := by positivity
  have h_l1_sum : Filter.Tendsto (fun k =>
      (∫ x in K_v_trans, |u k x - χ x|) + (∫ x in K, |u k x - χ x|))
      Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun k =>
        (∫ x in K_v_trans, |u k x - χ x|) + (∫ x in K, |u k x - χ x|))
        Filter.atTop (nhds ((0 : ℝ) + 0)) := h_l1_Kvt.add h_l1_K
    have h' : nhds ((0 : ℝ) + 0) = nhds (0 : ℝ) := by norm_num
    rw [h'] at h
    exact h
  have h_final : ∫ x in K, |χ' x - χ x| ≤ C := by
    by_contra h
    have h' : 0 < (∫ x in K, |χ' x - χ x|) - C := by linarith
    have h_ev2 : ∀ᶠ k in Filter.atTop,
        (∫ x in K_v_trans, |u k x - χ x|) + (∫ x in K, |u k x - χ x|) <
        (∫ x in K, |χ' x - χ x|) - C :=
      h_l1_sum (Iio_mem_nhds h')
    have h_ev3 : ∀ᶠ k in Filter.atTop, ∫ x in K, |χ' x - χ x| ≤
        ((∫ x in K_v_trans, |u k x - χ x|) + (∫ x in K, |u k x - χ x|)) + C :=
      Filter.eventually_atTop.mpr ⟨N, fun k hk => by
        have h := h_main_bound k hk
        have h_eq : ((∫ x in K_v_trans, |u k x - χ x|) + C) + (∫ x in K, |u k x - χ x|) =
            ((∫ x in K_v_trans, |u k x - χ x|) + (∫ x in K, |u k x - χ x|)) + C := by ring
        rw [h_eq] at h
        exact h⟩
    have h_ev4 := h_ev2.and h_ev3
    rcases Filter.eventually_atTop.mp h_ev4 with ⟨N', hN'⟩
    have h5 := hN' N' (by linarith)
    linarith
  rw [h_int_vol] at h_final
  have h10 : ENNReal.ofReal (volume DSet).toReal = volume DSet := by
    rw [ENNReal.ofReal_toReal hD_fin.ne]
  have h11 : ENNReal.ofReal C = (n : ENNReal) * ENNReal.ofReal ‖v‖ * perimeterIn S Ω := by
    have h12 : ((n : ENNReal) * perimeterIn S Ω) < ⊤ := hP_fin
    have h13 : ENNReal.ofReal C =
        ENNReal.ofReal ‖v‖ * ENNReal.ofReal (((n : ENNReal) * perimeterIn S Ω).toReal) := by
      simp only [C]
      rw [← ENNReal.ofReal_mul (show 0 ≤ ‖v‖ from by positivity)]
      <;> rfl
    rw [h13]
    rw [ENNReal.ofReal_toReal h12.ne]
    <;> ring
  have h13 : ENNReal.ofReal (volume DSet).toReal ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal h_final
  rw [h10, h11] at h13
  exact h13

end Geometry.Perimeter
