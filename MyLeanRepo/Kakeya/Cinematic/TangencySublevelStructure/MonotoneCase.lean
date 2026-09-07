import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.Basic

/-!
# Monotone case length bound

When the first derivative gap is large (L), the sublevel set is a single interval
with controlled length.
-/

namespace Kakeya.Cinematic

lemma monotone_case_length_bound
    {K : ℝ} (hK : 1 ≤ K)
    {I : ParameterInterval} {f g : C2Function} {t delta scale : ℝ}
    (ht_pos : 0 < t) (ht_eq : t = c2Distance f g) (hdelta : 0 < delta)
    (hI_short : I.IsShort K)
    (hL_h' : ∀ (x : UnitPoint), x ∈ I.carrier → (6 * K)⁻¹ * t ≤ |f.firstDeriv x - g.firstDeriv x|)
    (h_curv : ∀ (x : UnitPoint), K⁻¹ * t ≤ jetGap f g x)
    (E : Set UnitPoint)
    (hE : E = tangencySublevelSetOn I f g delta)
    (hE_closed : IsClosed E)
    (hE_nonempty : E.Nonempty)
    (C1 : ℝ) (hC1_large : 100 * K ≤ C1)
    (hscale : scale = Real.sqrt ((tangencyParameterOn I f g + delta) * t))
    (hdelta_le : delta ≤ (6 * K)⁻¹ * t) :
    ∃ (J : ParameterInterval), J.carrier = E ∧ J.length ≤ C1 * delta / scale := by
  let H : ℝ → ℝ := f.extension - g.extension
  let a := I.left
  let b := I.right
  let m : ℝ := (6 * K)⁻¹ * t
  have hK_pos : 0 < K := by linarith
  have hm_pos : 0 < m := by positivity
  have hH_c2 : ContDiff ℝ 2 H := ContDiff.sub f.extension_contDiff g.extension_contDiff
  have hH_diff1 : Differentiable ℝ H := hH_c2.differentiable (by norm_num)
  have hH_diff2 : Differentiable ℝ (deriv H) := by
    have h1 : ContDiff ℝ 1 (deriv H) := hH_c2.deriv'
    exact h1.differentiable (by norm_num)
  have h_deriv_eval : ∀ (x : UnitPoint), deriv H (x : ℝ) = f.firstDeriv x - g.firstDeriv x := by
    intro x
    have h_f_diff : Differentiable ℝ f.extension := f.extension_contDiff.differentiable (by norm_num)
    have h_g_diff : Differentiable ℝ g.extension := g.extension_contDiff.differentiable (by norm_num)
    have h1 : deriv H (x : ℝ) = deriv f.extension (x : ℝ) - deriv g.extension (x : ℝ) :=
      deriv_sub h_f_diff.differentiableAt h_g_diff.differentiableAt
    rw [h1]
    rw [C2Function.deriv_extension_eq_firstDeriv, C2Function.deriv_extension_eq_firstDeriv] <;> abel
  have h_deriv_lower : ∀ (r : ℝ), r ∈ Set.Icc a b → m ≤ |deriv H r| := by
    intro r hr
    let x : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have h_x_I : x ∈ I.carrier := by
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr
    have h : deriv H r = f.firstDeriv x - g.firstDeriv x := h_deriv_eval x
    rw [h]
    exact hL_h' x h_x_I
  have h_deriv_ne_zero : ∀ (r : ℝ), r ∈ Set.Icc a b → deriv H r ≠ 0 := by
    intro r hr
    have h1 : m ≤ |deriv H r| := h_deriv_lower r hr
    have h2 : 0 < |deriv H r| := by linarith
    exact abs_ne_zero.mp (ne_of_gt h2)
  have h_deriv_cont : ContinuousOn (deriv H) (Set.Icc a b) := hH_diff2.continuous.continuousOn
  have h_sign : (∀ r ∈ Set.Icc a b, 0 < deriv H r) ∨ (∀ r ∈ Set.Icc a b, deriv H r < 0) :=
    constant_sign_of_never_zero I.left_le_right h_deriv_cont h_deriv_ne_zero
  -- Length bound preliminaries (done early to avoid expensive typechecking in large context)
  have hΔ_attained : ∃ (xΔ : UnitPoint), xΔ ∈ I.centeredCarrier (1 / 2) ∧
      |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| = tangencyParameterOn I f g :=
    tangency_parameter_attained I f g
  rcases hΔ_attained with ⟨xΔ, hxΔ_centered, hΔ_eq⟩
  have hΔ_le : tangencyParameterOn I f g ≤ 2 * t := by
    have h1 : |f xΔ - g xΔ| ≤ c2Distance f g := abs_value_sub_le_c2Distance f g xΔ
    have h2 : |f.firstDeriv xΔ - g.firstDeriv xΔ| ≤ c2Distance f g := abs_firstDeriv_sub_le_c2Distance f g xΔ
    have h1' : |f xΔ - g xΔ| ≤ t := by exact ht_eq ▸ h1
    have h2' : |f.firstDeriv xΔ - g.firstDeriv xΔ| ≤ t := by exact ht_eq ▸ h2
    linarith [hΔ_eq]
  have hdelta_le_t : delta ≤ t := by
    have h4 : (6 * K)⁻¹ ≤ 1 := by
      have h5 : 1 ≤ 6 * K := by linarith
      have h6 : 0 < 6 * K := by positivity
      have h7 : (6 * K)⁻¹ * (6 * K) = 1 := by field_simp [h6.ne'] <;> ring
      nlinarith
    have h3 : (6 * K)⁻¹ * t ≤ t := by
      calc (6 * K)⁻¹ * t ≤ 1 * t := by gcongr
        _ = t := by ring
    exact le_trans hdelta_le h3
  have h_scale_pos : 0 < scale := by
    rw [hscale]
    have h1 : 0 ≤ |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| := by positivity
    have h2 : 0 < (|f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| + delta) * t := by
      apply mul_pos
      · linarith
      · exact ht_pos
    simpa [hΔ_eq] using Real.sqrt_pos.mpr h2
  -- Real projection of E
  let E_real : Set ℝ := {r | ∃ (x : UnitPoint), (x : ℝ) = r ∧ x ∈ E}
  have hE_real_def : E_real = {r ∈ Set.Icc a b | |H r| ≤ delta ∧ |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2} := by
    ext r
    simp only [E_real, Set.mem_setOf_eq, hE, tangencySublevelSetOn, ParameterInterval.centeredCarrier]
    constructor
    · rintro ⟨x, rfl, hx⟩
      have h1 : x ∈ I.carrier :=
        I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hx.1
      exact ⟨⟨h1.1, h1.2⟩, by
        have h2 : H (x : ℝ) = f x - g x := by simp [H]
        rw [h2]; exact hx.2, hx.1⟩
    · rintro ⟨hr, h_abs, h_centered⟩
      let x : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
      have h_x1 : x ∈ I.carrier := by
        simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr
      have h_x2 : x ∈ I.centeredCarrier (1 / 4) := h_centered
      have h_f_eq : f.extension r = f x := by
        have h : f.extension (x : ℝ) = f x := f.extension_eq_value x
        exact h
      have h_g_eq : g.extension r = g x := by
        have h : g.extension (x : ℝ) = g x := g.extension_eq_value x
        exact h
      have h3 : H r = f x - g x := by
        simp [H, h_f_eq, h_g_eq]
      refine' ⟨x, rfl, ⟨h_x2, _⟩⟩
      have h4 : |f x - g x| ≤ delta := by
        rw [←h3]
        exact h_abs
      exact h4
  -- H is monotone or antitone on [a,b] based on derivative sign
  have hH_contOn : ContinuousOn H (Set.Icc a b) := hH_diff1.continuous.continuousOn
  have hH_diffOn : DifferentiableOn ℝ H (interior (Set.Icc a b)) := hH_diff1.differentiableOn
  have h_mono_or_anti : MonotoneOn H (Set.Icc a b) ∨ AntitoneOn H (Set.Icc a b) := by
    rcases h_sign with (h_pos | h_neg)
    · have h_nonneg : ∀ x ∈ interior (Set.Icc a b), 0 ≤ deriv H x := by
        intro x hx
        have h_x_Icc : x ∈ Set.Icc a b := interior_subset hx
        exact le_of_lt (h_pos x h_x_Icc)
      exact Or.inl (monotoneOn_of_deriv_nonneg (convex_Icc a b) hH_contOn hH_diffOn h_nonneg)
    · have h_nonpos : ∀ x ∈ interior (Set.Icc a b), deriv H x ≤ 0 := by
        intro x hx
        have h_x_Icc : x ∈ Set.Icc a b := interior_subset hx
        exact le_of_lt (h_neg x h_x_Icc)
      exact Or.inr (antitoneOn_of_deriv_nonpos (convex_Icc a b) hH_contOn hH_diffOn h_nonpos)
  let R := (1 / 4 : ℝ) * I.length / 2
  -- {r ∈ Icc a b | |H r| ≤ delta} is convex
  have h_abs_convex : Convex ℝ {r ∈ Set.Icc a b | |H r| ≤ delta} := by
    rcases h_mono_or_anti with (h_mono | h_anti)
    · have h1 : Convex ℝ {r ∈ Set.Icc a b | H r ≤ delta} := h_mono.convex_le (convex_Icc a b) delta
      have h2 : Convex ℝ {r ∈ Set.Icc a b | -delta ≤ H r} := h_mono.convex_ge (convex_Icc a b) (-delta)
      have h3 : {r ∈ Set.Icc a b | |H r| ≤ delta} =
          {r ∈ Set.Icc a b | H r ≤ delta} ∩ {r ∈ Set.Icc a b | -delta ≤ H r} := by
        ext r
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
        <;> aesop
      rw [h3]; exact h1.inter h2
    · have h1 : Convex ℝ {r ∈ Set.Icc a b | H r ≤ delta} := h_anti.convex_le (convex_Icc a b) delta
      have h2 : Convex ℝ {r ∈ Set.Icc a b | -delta ≤ H r} := h_anti.convex_ge (convex_Icc a b) (-delta)
      have h3 : {r ∈ Set.Icc a b | |H r| ≤ delta} =
          {r ∈ Set.Icc a b | H r ≤ delta} ∩ {r ∈ Set.Icc a b | -delta ≤ H r} := by
        ext r
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
        <;> aesop
      rw [h3]; exact h1.inter h2
  -- Centered set is convex
  have h_centered_convex : Convex ℝ {r : ℝ | |r - I.midpoint| ≤ R} := by
    have h4 : {r : ℝ | |r - I.midpoint| ≤ R} = Set.Icc (I.midpoint - R) (I.midpoint + R) := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by linarith, by linarith⟩
    rw [h4]; exact convex_Icc _ _
  -- E_real is convex
  have h_conv : Convex ℝ E_real := by
    rw [hE_real_def]
    have h5 : {r ∈ Set.Icc a b | |H r| ≤ delta ∧ |r - I.midpoint| ≤ R} =
        {r ∈ Set.Icc a b | |H r| ≤ delta} ∩ {r : ℝ | |r - I.midpoint| ≤ R} := by
      ext r
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro h
        exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
      · intro h
        exact ⟨h.1.1, h.1.2, h.2⟩
    rw [h5]; exact h_abs_convex.inter h_centered_convex
  -- E_real is closed
  have hE_real_closed : IsClosed E_real := by
    have h_cont1 : Continuous (fun r : ℝ => |H r|) :=
      continuous_abs.comp hH_diff1.continuous
    have h_cont2 : Continuous (fun r : ℝ => |r - I.midpoint|) :=
      continuous_abs.comp (continuous_id.sub continuous_const)
    have h : IsClosed ({r : ℝ | |H r| ≤ delta} : Set ℝ) :=
      IsClosed.preimage h_cont1 isClosed_Iic
    have h2 : IsClosed ({r : ℝ | |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2} : Set ℝ) :=
      IsClosed.preimage h_cont2 isClosed_Iic
    rw [hE_real_def]
    have hIcc : IsClosed (Set.Icc a b) := isClosed_Icc
    have h_set_eq : {r : ℝ | r ∈ Set.Icc a b ∧ |H r| ≤ delta ∧ |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2} =
        Set.Icc a b ∩ {r : ℝ | |H r| ≤ delta} ∩ {r : ℝ | |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2} := by
      ext x
      simp [Set.mem_inter_iff]
      <;> tauto
    rw [h_set_eq]
    exact (hIcc.inter h).inter h2
  -- E_real nonempty
  have hE_real_nonempty : E_real.Nonempty := by
    rcases hE_nonempty with ⟨x, hx⟩
    exact ⟨(x : ℝ), ⟨x, rfl, hx⟩⟩
  have hE_real_bdd : BddAbove E_real := ⟨b, fun r hr => (hE_real_def ▸ hr).1.2⟩
  have hE_real_bdd2 : BddBelow E_real := ⟨a, fun r hr => (hE_real_def ▸ hr).1.1⟩
  let c := sInf E_real
  let d := sSup E_real
  have hc_in : c ∈ E_real := by
    have h : c ∈ closure E_real := csInf_mem_closure hE_real_nonempty hE_real_bdd2
    have h' : closure E_real = E_real := hE_real_closed.closure_eq
    rw [h'] at h
    exact h
  have hd_in : d ∈ E_real := by
    have h : d ∈ closure E_real := csSup_mem_closure hE_real_nonempty hE_real_bdd
    have h' : closure E_real = E_real := hE_real_closed.closure_eq
    rw [h'] at h
    exact h
  have hcd : c ≤ d := Real.sInf_le_sSup E_real hE_real_bdd2 hE_real_bdd
  have hE_real_eq : E_real = Set.Icc c d := by
    apply Set.Subset.antisymm
    · exact subset_Icc_csInf_csSup hE_real_bdd2 hE_real_bdd
    · intro r hr
      have h1 : c ≤ r := hr.1
      have h2 : r ≤ d := hr.2
      by_cases hcd_eq : c = d
      · have hr_eq : r = c := by linarith
        rw [hr_eq]
        exact hc_in
      · have hcd_lt : c < d := lt_of_le_of_ne hcd hcd_eq
        set a : ℝ := (d - r) / (d - c) with ha_def
        set b : ℝ := (r - c) / (d - c) with hb_def
        have ha_nonneg : 0 ≤ a := by
          rw [ha_def]
          apply div_nonneg <;> linarith
        have hb_nonneg : 0 ≤ b := by
          rw [hb_def]
          apply div_nonneg <;> linarith
        have hab_sum : a + b = 1 := by
          rw [ha_def, hb_def]
          field_simp [hcd_lt.ne'] <;> ring
        have hcomb : a * c + b * d = r := by
          rw [ha_def, hb_def]
          field_simp [hcd_lt.ne'] <;> ring
        have h_in : a • c + b • d ∈ E_real := h_conv hc_in hd_in ha_nonneg hb_nonneg hab_sum
        have h_smul : a • c + b • d = a * c + b * d := by simp
        rw [h_smul, hcomb] at h_in
        exact h_in
  have hca : 0 ≤ c := by
    have h3 : c ∈ Set.Icc a b := (hE_real_def ▸ hc_in).1
    linarith [I.left_mem.1, h3.1]
  have hcb : c ≤ 1 := by
    have h3 : c ∈ Set.Icc a b := (hE_real_def ▸ hc_in).1
    linarith [I.right_mem.2, h3.2]
  have hda : 0 ≤ d := by
    have h3 : d ∈ Set.Icc a b := (hE_real_def ▸ hd_in).1
    linarith [I.left_mem.1, h3.1]
  have hdb : d ≤ 1 := by
    have h3 : d ∈ Set.Icc a b := (hE_real_def ▸ hd_in).1
    linarith [I.right_mem.2, h3.2]
  let J : ParameterInterval := ⟨c, d, ⟨hca, hcb⟩, ⟨hda, hdb⟩, hcd⟩
  have hJ_carrier : J.carrier = E := by
    ext x
    simp only [J, ParameterInterval.carrier, Set.mem_setOf_eq]
    constructor
    · intro hx
      have h1 : (x : ℝ) ∈ Set.Icc c d := hx
      have h2 : (x : ℝ) ∈ E_real := by rw [hE_real_eq]; exact h1
      rcases h2 with ⟨y, hy_eq, hy_E⟩
      have h3 : y = x := Subtype.ext hy_eq
      rw [h3] at hy_E
      exact hy_E
    · intro hx
      have h1 : (x : ℝ) ∈ E_real := ⟨x, rfl, hx⟩
      rw [hE_real_eq] at h1
      exact h1
  -- MVT: |H(d) - H(c)| ≥ m * (d - c)
  have h_len_bound : d - c ≤ 2 * delta / m := by
    by_cases hcd' : c = d
    · have h_zero : d - c = 0 := by linarith
      rw [h_zero]
      positivity
    · have hcd_lt : c < d := lt_of_le_of_ne hcd hcd'
      have h_mvt : ∃ ξ ∈ Set.Ioo c d, deriv H ξ = (H d - H c) / (d - c) :=
        exists_hasDerivAt_eq_slope (a := c) (b := d) (f := H) (f' := deriv H) hcd_lt
          hH_diff1.continuous.continuousOn
          (fun z _ => hH_diff1.differentiableAt.hasDerivAt)
      rcases h_mvt with ⟨ξ, hξ_Ioo, h_slope⟩
      have h_eq : H d - H c = deriv H ξ * (d - c) := by
        rw [h_slope]
        field_simp [hcd_lt.ne'] <;> ring
      have hξ_Icc : ξ ∈ Set.Icc a b :=
        ⟨by linarith [(hE_real_def ▸ hc_in).1.1, hξ_Ioo.1],
         by linarith [(hE_real_def ▸ hd_in).1.2, hξ_Ioo.2]⟩
      have h_deriv_low : m ≤ |deriv H ξ| := h_deriv_lower ξ hξ_Icc
      have h1 : |H d - H c| = |deriv H ξ| * (d - c) := by
        rw [h_eq, abs_mul, abs_of_pos (show 0 < d - c by linarith)]
      have h2 : m * (d - c) ≤ |H d - H c| := by rw [h1] <;> gcongr
      have h3 : |H d| ≤ delta := (hE_real_def ▸ hd_in).2.1
      have h4 : |H c| ≤ delta := (hE_real_def ▸ hc_in).2.1
      have h5 : |H d - H c| ≤ 2 * delta := by
        calc |H d - H c| ≤ |H d| + |H c| := by exact abs_sub (H d) (H c)
          _ ≤ 2 * delta := by linarith
      have h6 : m * (d - c) ≤ 2 * delta := by linarith
      have h7 : d - c ≤ 2 * delta / m := by
        calc d - c
          = (m * (d - c)) / m := by field_simp [hm_pos.ne'] <;> ring
        _ ≤ (2 * delta) / m := by gcongr
      exact h7
  -- Convert: 2δ/m = 12Kδ/t ≤ C1δ/scale
  have h_main : d - c ≤ C1 * delta / scale := by
    have h9 : 2 * delta / m = 12 * K * delta / t := by
      simp [m] <;> field_simp [hK_pos.ne'] <;> ring
    rw [h9] at h_len_bound
    have h_scale_le : scale ≤ Real.sqrt 3 * t :=
      scale_le_sqrt3_t ht_pos hdelta hΔ_le hdelta_le_t hscale
    have h23 : 12 * K * delta / t ≤ C1 * delta / scale :=
      abstract_scale_bound hK ht_pos hdelta h_scale_pos hC1_large h_scale_le
    exact le_trans h_len_bound h23
  have hJ_len : J.length ≤ C1 * delta / scale := by
    have h : J.length = d - c := by
      simp [J, ParameterInterval.length] <;> ring
    rw [h]
    exact h_main
  exact ⟨J, hJ_carrier, hJ_len⟩

end Kakeya.Cinematic
