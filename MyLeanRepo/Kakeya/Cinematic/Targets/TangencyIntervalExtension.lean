import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.TangencyIntervalExtension.Calculus

/-!
# Tangency interval extension

This target is PYZ Lemma 18: closeness on an interval propagates to a centered
dilation with quadratic loss in the dilation factor.
-/

namespace Kakeya.Cinematic

theorem tangency_interval_extension :
    TangencyIntervalExtensionStatement := by
  intro K D hK hD
  refine ⟨3 + 48 * K, by positivity, ?_⟩
  intro family hfamily I hI f hf g hg hfg delta hdelta hdelta_upper
    J hJ_subset hclose lambda hlambda x hxI hxJ
  let H : ℝ → ℝ := f.extension - g.extension
  let t : ℝ := c2Distance f g
  have hKpos : 0 < K := by linarith
  have htpos : 0 < t := by
    simpa [t, c2Distance_eq_dist] using dist_pos.mpr hfg
  have hdelta_t : delta ≤ t / (6 * K) := by
    simpa [t] using hdelta_upper
  have hIshort : I.length ≤ (6 * K)⁻¹ := hI.2
  let leftPoint : UnitPoint := ⟨J.left, J.left_mem⟩
  let rightPoint : UnitPoint := ⟨J.right, J.right_mem⟩
  have hleft_carrier : leftPoint ∈ J.carrier := by
    exact ⟨le_rfl, J.left_le_right⟩
  have hright_carrier : rightPoint ∈ J.carrier := by
    exact ⟨J.left_le_right, le_rfl⟩
  have hleft_centered := hJ_subset hleft_carrier
  have hright_centered := hJ_subset hright_carrier
  have hJ_length_quarter : J.length ≤ I.length / 4 := by
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq,
      ParameterInterval.length] at hleft_centered hright_centered
    dsimp only [leftPoint, rightPoint] at hleft_centered hright_centered
    have hleft_bounds := abs_le.mp hleft_centered
    have hright_bounds := abs_le.mp hright_centered
    simp only [ParameterInterval.length]
    linarith
  have hJ_length_upper : J.length ≤ 1 / (24 * K) := by
    have hshort : I.length ≤ 1 / (6 * K) := by
      simpa [one_div] using hIshort
    calc
      J.length ≤ I.length / 4 := hJ_length_quarter
      _ ≤ (1 / (6 * K)) / 4 := by gcongr
      _ = 1 / (24 * K) := by
        field_simp [hKpos.ne']
        <;> ring
  by_cases hJzero : J.length = 0
  · have hleft_eq_right : J.left = J.right := by
      exact (sub_eq_zero.mp (by simpa [ParameterInterval.length] using hJzero)).symm
    have hx_zero : |(x : ℝ) - J.midpoint| = 0 := by
      have hx_nonpos : |(x : ℝ) - J.midpoint| ≤ 0 := by
        calc
          |(x : ℝ) - J.midpoint|
              ≤ lambda * J.length / 2 := hxJ
          _ = 0 := by rw [hJzero]; ring
      apply le_antisymm
      · exact hx_nonpos
      · exact abs_nonneg _
    have hx_midpoint : (x : ℝ) = J.midpoint := by
      exact sub_eq_zero.mp (abs_eq_zero.mp hx_zero)
    have hx_carrier : x ∈ J.carrier := by
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
      simp only [ParameterInterval.midpoint] at hx_midpoint
      constructor <;> linarith
    have hx_close := hclose x hx_carrier
    have hlambda_sq : 1 ≤ lambda ^ 2 := by nlinarith
    have hconstant : 1 ≤ 3 + 48 * K := by linarith
    have hscale : 1 ≤ (3 + 48 * K) * lambda ^ 2 := by
      nlinarith
    calc
      |f x - g x| ≤ delta := hx_close
      _ ≤ (3 + 48 * K) * lambda ^ 2 * delta := by
        simpa using mul_le_mul_of_nonneg_right hscale hdelta.le
  · have hJpos : 0 < J.length :=
      lt_of_le_of_ne J.length_nonneg (Ne.symm hJzero)
    have hsquare :
        t * J.length ^ 2 ≤ 48 * K * delta := by
      by_contra hnot
      have hlarge :
          48 * K * delta < t * J.length ^ 2 := lt_of_not_ge hnot
      have hf2 : ContDiff ℝ 2 f.extension := f.extension_contDiff
      have hg2 : ContDiff ℝ 2 g.extension := g.extension_contDiff
      have hH2 : ContDiff ℝ 2 H := hf2.sub hg2
      have hH1diff : Differentiable ℝ H :=
        hH2.differentiable (by norm_num)
      have hH2diff : Differentiable ℝ (deriv H) :=
        hH2.differentiable_deriv_two
      have hf_diff : Differentiable ℝ f.extension :=
        hf2.differentiable (by norm_num)
      have hg_diff : Differentiable ℝ g.extension :=
        hg2.differentiable (by norm_num)
      have hf_deriv_diff : Differentiable ℝ (deriv f.extension) :=
        hf2.differentiable_deriv_two
      have hg_deriv_diff : Differentiable ℝ (deriv g.extension) :=
        hg2.differentiable_deriv_two
      have hH_value (y : UnitPoint) :
          H y = f y - g y := by
        simp [H]
      have hH_deriv (y : UnitPoint) :
          deriv H y = f.firstDeriv y - g.firstDeriv y := by
        rw [show H = f.extension - g.extension by rfl]
        rw [deriv_sub hf_diff.differentiableAt hg_diff.differentiableAt]
        simp
      have hH_second (y : UnitPoint) :
          deriv (deriv H) y = f.secondDeriv y - g.secondDeriv y := by
        have hderiv :
            deriv H = deriv f.extension - deriv g.extension := by
          funext z
          rw [show H = f.extension - g.extension by rfl]
          exact deriv_sub hf_diff.differentiableAt hg_diff.differentiableAt
        rw [hderiv]
        rw [deriv_sub hf_deriv_diff.differentiableAt
          hg_deriv_diff.differentiableAt]
        simp
      have hleft_lt_right : J.left < J.right := by
        simpa [ParameterInterval.length] using hJpos
      have hmvt :
          ∃ c ∈ Set.Ioo J.left J.right,
            deriv H c = (H J.right - H J.left) / (J.right - J.left) :=
        exists_deriv_eq_slope H hleft_lt_right
          hH1diff.continuous.continuousOn hH1diff.differentiableOn
      rcases hmvt with ⟨c, hc, hc_slope⟩
      have hc01 : c ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;>
          linarith [J.left_mem.1, J.right_mem.2, hc.1, hc.2]
      let cp : UnitPoint := ⟨c, hc01⟩
      have hcp_carrier : cp ∈ J.carrier := by
        exact ⟨hc.1.le, hc.2.le⟩
      have hleft_bound : |H J.left| ≤ delta := by
        rw [hH_value leftPoint]
        exact hclose leftPoint hleft_carrier
      have hright_bound : |H J.right| ≤ delta := by
        rw [hH_value rightPoint]
        exact hclose rightPoint hright_carrier
      have hslope_bound :
          |deriv H c| ≤ 2 * delta / J.length := by
        rw [hc_slope]
        rw [show J.right - J.left = J.length by rfl]
        rw [abs_div, abs_of_pos hJpos]
        calc
          |H J.right - H J.left| / J.length
              ≤ (|H J.right| + |H J.left|) / J.length := by
                gcongr
                exact abs_sub _ _
          _ ≤ (delta + delta) / J.length := by gcongr
          _ = 2 * delta / J.length := by ring
      have hratio :
          2 * delta / J.length <
            t * J.length / (24 * K) := by
        have hdenom : 0 < 24 * K := by positivity
        have hscaled :
            2 * delta < t * J.length ^ 2 / (24 * K) := by
          apply (lt_div_iff₀ hdenom).2
          nlinarith
        calc
          2 * delta / J.length
              < (t * J.length ^ 2 / (24 * K)) / J.length := by
                exact div_lt_div_of_pos_right hscaled hJpos
          _ = t * J.length / (24 * K) := by
                field_simp [hJpos.ne', hKpos.ne']
                <;> ring
      have hinv_le_one : 1 / (24 * K) ≤ 1 := by
        exact (div_le_one (by positivity)).2 (by linarith)
      have hlinear_scale :
          t * J.length / (24 * K) + t * J.length ≤
            t / (12 * K) := by
        calc
          t * J.length / (24 * K) + t * J.length
              = t * J.length * (1 / (24 * K) + 1) := by ring
          _ ≤ t * (1 / (24 * K)) * (1 / (24 * K) + 1) := by
                gcongr
          _ ≤ t * (1 / (24 * K)) * 2 := by
                gcongr
                linarith
          _ = t / (12 * K) := by
                field_simp [hKpos.ne']
                <;> ring
      have hprime_small :
          ∀ y : UnitPoint, y ∈ J.carrier →
            |f.firstDeriv y - g.firstDeriv y| ≤ t / (12 * K) := by
        intro y hy
        have hydist : |(y : ℝ) - c| ≤ J.length := by
          rw [abs_le]
          simp only [ParameterInterval.length]
          constructor <;> linarith [hy.1, hy.2, hc.1, hc.2]
        have hlip :=
          lipschitz_deriv f g y cp
        have htriangle :
            |f.firstDeriv y - g.firstDeriv y| ≤
              |f.firstDeriv cp - g.firstDeriv cp| +
                |(f.firstDeriv y - g.firstDeriv y) -
                  (f.firstDeriv cp - g.firstDeriv cp)| := by
          calc
            |f.firstDeriv y - g.firstDeriv y| =
                |(f.firstDeriv cp - g.firstDeriv cp) +
                  ((f.firstDeriv y - g.firstDeriv y) -
                    (f.firstDeriv cp - g.firstDeriv cp))| := by
                      congr 1
                      ring
            _ ≤ |f.firstDeriv cp - g.firstDeriv cp| +
                  |(f.firstDeriv y - g.firstDeriv y) -
                    (f.firstDeriv cp - g.firstDeriv cp)| :=
                abs_add_le _ _
        have hcp_deriv :
            |f.firstDeriv cp - g.firstDeriv cp| ≤
              2 * delta / J.length := by
          rw [← hH_deriv cp]
          exact hslope_bound
        calc
          |f.firstDeriv y - g.firstDeriv y|
              ≤ |f.firstDeriv cp - g.firstDeriv cp| +
                  |(f.firstDeriv y - g.firstDeriv y) -
                    (f.firstDeriv cp - g.firstDeriv cp)| := htriangle
          _ ≤ 2 * delta / J.length +
                t * |(y : ℝ) - (cp : ℝ)| := by
              gcongr
          _ ≤ 2 * delta / J.length + t * J.length := by
              gcongr
          _ ≤ t * J.length / (24 * K) + t * J.length := by
              linarith
          _ ≤ t / (12 * K) := hlinear_scale
      have hsecond_large :
          ∀ y : UnitPoint, y ∈ J.carrier →
            t / (2 * K) ≤ |f.secondDeriv y - g.secondDeriv y| := by
        intro y hy
        have hcurvature := hfamily.2.2 hf hg y
        have hvalue : |f y - g y| ≤ delta := hclose y hy
        have hprime := hprime_small y hy
        have hjet :
            K⁻¹ * t ≤
              |f y - g y| +
                |f.firstDeriv y - g.firstDeriv y| +
                  |f.secondDeriv y - g.secondDeriv y| := by
          simpa [t, jetGap] using hcurvature
        have hkinv : K⁻¹ * t = t / K := by
          field_simp [hKpos.ne']
        have halgebra :
            t / K - t / (6 * K) - t / (12 * K) =
              3 * t / (4 * K) := by
          field_simp [hKpos.ne']
          <;> ring
        have hthree :
            3 * t / (4 * K) ≤
              |f.secondDeriv y - g.secondDeriv y| := by
          rw [hkinv] at hjet
          rw [← halgebra]
          linarith [hdelta_t]
        have hhalf : t / (2 * K) ≤ 3 * t / (4 * K) := by
          have hnonneg : 0 ≤ t / (4 * K) := by positivity
          have hdiff :
              3 * t / (4 * K) - t / (2 * K) = t / (4 * K) := by
            field_simp [hKpos.ne']
            <;> ring
          linarith
        exact hhalf.trans hthree
      have hsecond_real :
          ∀ z ∈ Set.Icc J.left J.right,
            t / (2 * K) ≤ |deriv (deriv H) z| := by
        intro z hz
        have hz01 : z ∈ Set.Icc (0 : ℝ) 1 := by
          exact ⟨J.left_mem.1.trans hz.1, hz.2.trans J.right_mem.2⟩
        let zp : UnitPoint := ⟨z, hz01⟩
        have hzp_carrier : zp ∈ J.carrier := hz
        rw [hH_second zp]
        exact hsecond_large zp hzp_carrier
      have hsecond_ne :
          ∀ z ∈ Set.Icc J.left J.right,
            deriv (deriv H) z ≠ 0 := by
        intro z hz hzero
        have hlower := hsecond_real z hz
        rw [hzero, abs_zero] at hlower
        have : 0 < t / (2 * K) := by positivity
        linarith
      have hsign :=
        constant_sign_of_never_zero J.left_le_right
          (hH2.deriv'.continuous_deriv_one.continuousOn) hsecond_ne
      have hbound_real :
          ∀ z ∈ Set.Icc J.left J.right, |H z| ≤ delta := by
        intro z hz
        have hz01 : z ∈ Set.Icc (0 : ℝ) 1 := by
          exact ⟨J.left_mem.1.trans hz.1, hz.2.trans J.right_mem.2⟩
        let zp : UnitPoint := ⟨z, hz01⟩
        have hzp_carrier : zp ∈ J.carrier := hz
        rw [hH_value zp]
        exact hclose zp hzp_carrier
      have hquadratic :
          t / (2 * K) * J.length ^ 2 ≤ 16 * delta := by
        rcases hsign with hpositive | hnegative
        · apply interval_sq_le_of_second_deriv_lower
            hH1diff hH2diff J.left_le_right hbound_real
          intro z hz
          have habs := hsecond_real z hz
          have hpos := hpositive z hz
          rw [abs_of_pos hpos] at habs
          exact habs
        · have hneg1 : Differentiable ℝ (-H) := hH1diff.neg
          have hneg2 : Differentiable ℝ (deriv (-H)) := by
            have heq : deriv (-H) = -deriv H := by
              funext z
              simp
            rw [heq]
            exact hH2diff.neg
          apply interval_sq_le_of_second_deriv_lower
            hneg1 hneg2 J.left_le_right
          · intro z hz
            simpa using hbound_real z hz
          · intro z hz
            have habs := hsecond_real z hz
            have hneg := hnegative z hz
            have hsecond_neg :
                deriv (deriv (-H)) z = -deriv (deriv H) z := by
              have heq : deriv (-H) = -deriv H := by
                funext w
                simp
              rw [heq]
              simp
            rw [hsecond_neg]
            rw [abs_of_neg hneg] at habs
            exact habs
      have hsmall :
          t * J.length ^ 2 ≤ 32 * K * delta := by
        calc
          t * J.length ^ 2
              = (2 * K) *
                  (t / (2 * K) * J.length ^ 2) := by
                    field_simp [hKpos.ne']
                    <;> ring
          _ ≤ (2 * K) * (16 * delta) := by
                gcongr
          _ = 32 * K * delta := by ring
      have h32le48 : 32 * K * delta ≤ 48 * K * delta := by
        have hKdelta : 0 ≤ K * delta :=
          mul_nonneg hKpos.le hdelta.le
        calc
          32 * K * delta = 32 * (K * delta) := by ring
          _ ≤ 48 * (K * delta) :=
            mul_le_mul_of_nonneg_right (by norm_num) hKdelta
          _ = 48 * K * delta := by ring
      exact (not_lt_of_ge (hsmall.trans h32le48)) hlarge
    have hA : 0 ≤ 48 * K := by positivity
    have hresult :=
      value_bound_on_centered_dilation f g J hdelta.le hA hJpos
        hclose (by simpa [t] using hsquare) hlambda hxJ
    simpa [add_assoc] using hresult

end Kakeya.Cinematic
