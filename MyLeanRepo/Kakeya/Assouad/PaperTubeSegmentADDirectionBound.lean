import MyLeanRepo.Kakeya.Assouad.WZLemma30ADUpper
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.ADCoveringComparisonWithConstant
import MyLeanRepo.Kakeya.Assouad.TubeSegmentProjectionCoveringLowerBound
import MyLeanRepo.Kakeya.Assouad.TubeSegmentProjectionLocalization

/-!
# Paper-carrier (6δ) direction bound for WZ2 Section 6 Step 4

Adapts `tube_segment_ad_direction_bound` to paper tube carriers, which are
`6δ`-thickenings rather than `δ`-thickenings.

Key trick: call the covering lower bound with carrier thickness `6*delta` but
density `lambda = delta^epsilon`. The mass requirement becomes
`36 * delta^epsilon * delta^2 * sqrt(rho)`, which the paper-carrier witness
meets. The conclusion exponent and constant are unchanged.

Additional assumption: `6 * delta ≤ rho` (needed for localization radius).
-/

noncomputable section

namespace Kakeya.Assouad

/--
Power-form direction bound for paper (6δ) carriers.

Same conclusion as `TubeSegmentADDirectionPowerStatement` but the input set
lives in a `6*delta`-thick tube segment and the mass lower bound has a
factor of `36`.
-/
theorem paper_tube_segment_ad_direction_power :
    TubeSegmentProjectionCoveringLowerBoundStatement →
      TubeSegmentProjectionLocalizationStatement →
        ADCoveringComparisonWithConstantStatement →
          ∀ (delta rho epsilon alpha start : ℝ),
            0 < delta → 6 * delta ≤ rho → rho ≤ 1 / 4 →
            0 < epsilon → 0 < alpha → alpha < 1 →
            ∀ (base direction v : Point3),
              ‖direction‖ = 1 → ‖v‖ = 1 →
              ∀ E : Set Point3,
                MeasurableSet E →
                E ⊆ tubeSegmentCarrier (6 * delta) base direction start rho →
                ENNReal.ofReal
                    (36 * Real.rpow delta epsilon * delta ^ 2 *
                      Real.sqrt rho) ≤
                  MeasureTheory.volume E →
                IsADSet1 (scalarProjection v E) rho alpha
                    (Kakeya.realRpowENN delta (-epsilon)) →
                  Kakeya.realRpowENN
                      (|inner ℝ direction v| / Real.sqrt rho)
                      (1 - alpha) ≤
                    20000 * Kakeya.realRpowENN delta (-2 * epsilon) := by
  intro h_lower h_loc h_cmp
  intro delta rho epsilon alpha start hdelta h6delta_rho hrho_quarter
    hepsilon halpha halpha_lt_one base direction v hdir hv E hEmeas
    hEsub hvol hAD
  set tau : ℝ := |inner ℝ direction v| with htau_def
  set x : ℝ := tau / Real.sqrt rho with hx_def
  have hrho_pos : 0 < rho := by linarith
  have hrho_nonneg : 0 ≤ rho := by linarith
  have hsqrt_rho_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have hx_nonneg : 0 ≤ x := by positivity
  have hdelta_one : delta ≤ 1 := by linarith
  have hrho_one : rho ≤ 1 := by linarith
  have hsqrt_sq : Real.sqrt rho * Real.sqrt rho = rho :=
    Real.mul_self_sqrt hrho_nonneg
  by_cases h_case : tau < Real.sqrt rho
  · -- Case 1: tau < sqrt rho, trivial
    have hx_le_one : x ≤ 1 := by
      rw [hx_def]
      exact (div_le_one hsqrt_rho_pos).mpr h_case.le
    have h_exp_nonneg : 0 ≤ 1 - alpha := by linarith
    have h1 : Real.rpow x (1 - alpha) ≤ 1 :=
      Real.rpow_le_one hx_nonneg hx_le_one h_exp_nonneg
    have h2 : 1 ≤ Real.rpow delta (-2 * epsilon) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdelta_one (by linarith)
    have h_main1 : Kakeya.realRpowENN x (1 - alpha) ≤ 1 := by
      simp only [Kakeya.realRpowENN, ENNReal.ofReal_le_one]
      exact h1
    have h3 : (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-2 * epsilon) := by
      simp only [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
      exact h2
    have h4 : (1 : ENNReal) ≤ 20000 * Kakeya.realRpowENN delta (-2 * epsilon) := by
      have h5 : (1 : ENNReal) ≤ (20000 : ENNReal) := by norm_num
      have h6 : (1 : ENNReal) * Kakeya.realRpowENN delta (-2 * epsilon) ≤
          (20000 : ENNReal) * Kakeya.realRpowENN delta (-2 * epsilon) :=
        mul_le_mul_of_nonneg_right h5 (by simp)
      have h7 : (1 : ENNReal) * Kakeya.realRpowENN delta (-2 * epsilon) =
          Kakeya.realRpowENN delta (-2 * epsilon) := by simp
      rw [h7] at h6
      exact h3.trans h6
    exact h_main1.trans h4
  · -- Case 2: tau ≥ sqrt rho
    have htau_ge : Real.sqrt rho ≤ tau := by linarith
    set lambda : ℝ := Real.rpow delta epsilon with hlambda_def
    have hlambda_pos : 0 < lambda := Real.rpow_pos_of_pos hdelta epsilon
    have hlambda_one : lambda ≤ 1 := by
      rw [hlambda_def]
      exact Real.rpow_le_one hdelta.le hdelta_one hepsilon.le
    set N : ENNReal :=
      (↑(Metric.externalCoveringNumber
        ⟨rho, hrho_nonneg⟩ (scalarProjection v E)) : ENNReal) with hN_def

    -- Covering lower bound with carrier thickness 6*delta, density lambda
    have h6delta_pos : 0 < 6 * delta := by positivity
    have h6delta_rho : 6 * delta ≤ rho := h6delta_rho
    have hvol' :
        ENNReal.ofReal (lambda * (6 * delta) ^ 2 * Real.sqrt rho) ≤
          MeasureTheory.volume E := by
      have h_eq : lambda * (6 * delta) ^ 2 * Real.sqrt rho =
          36 * lambda * delta ^ 2 * Real.sqrt rho := by ring
      rw [h_eq]
      exact hvol
    have h_lower1 :
        ENNReal.ofReal (lambda * tau * Real.sqrt rho) ≤
          10000 * ENNReal.ofReal rho * N := by
      simpa [hN_def, hlambda_def] using
        h_lower (6 * delta) rho lambda start h6delta_pos h6delta_rho hrho_one
          hlambda_pos hlambda_one base direction v hdir hv htau_ge
          E hEmeas hEsub hvol'

    have hx_sqrt : x * Real.sqrt rho = tau := by
      rw [hx_def]
      field_simp [hsqrt_rho_pos.ne']
    have halgebra :
        lambda * tau * Real.sqrt rho = rho * (lambda * x) := by
      calc
        lambda * tau * Real.sqrt rho
            = lambda * (x * Real.sqrt rho) * Real.sqrt rho := by rw [hx_sqrt]
        _ = lambda * x * (Real.sqrt rho * Real.sqrt rho) := by ring
        _ = lambda * x * rho := by rw [hsqrt_sq]
        _ = rho * (lambda * x) := by ring
    have h_ofReal :
        ENNReal.ofReal (rho * (lambda * x)) =
          ENNReal.ofReal rho *
            (ENNReal.ofReal lambda * ENNReal.ofReal x) := by
      rw [ENNReal.ofReal_mul hrho_nonneg,
        ENNReal.ofReal_mul (by positivity : 0 ≤ lambda)]
    have hlambda_enn :
        ENNReal.ofReal lambda = Kakeya.realRpowENN delta epsilon := by
      simp [lambda, Kakeya.realRpowENN]
    have h_lower2 :
        ENNReal.ofReal rho *
            (Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x) ≤
          ENNReal.ofReal rho * (10000 * N) := by
      rw [halgebra, h_ofReal, hlambda_enn] at h_lower1
      simpa [mul_assoc, mul_comm, mul_left_comm] using h_lower1
    have hrho_ne_zero : ENNReal.ofReal rho ≠ 0 := by positivity
    have h_lower3 :
        Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x ≤
          10000 * N := by
      have h9 :
          (Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x) *
              ENNReal.ofReal rho ≤
            (10000 * N) * ENNReal.ofReal rho := by
          simpa [mul_assoc, mul_comm, mul_left_comm] using h_lower2
      exact (ENNReal.mul_le_mul_iff_left hrho_ne_zero
        ENNReal.ofReal_ne_top).mp h9

    -- Localization with carrier thickness 6*delta
    set center : ℝ :=
      inner ℝ
        (base + (start + Real.sqrt rho / 2) • direction) v
    have hloc1 :
        scalarProjection v E ⊆
          Metric.closedBall center
            (6 * delta + tau * Real.sqrt rho / 2) := by
      exact (Set.image_mono hEsub).trans
        (h_loc (6 * delta) rho start (by linarith) hrho_nonneg
          base direction v hv)
    set R : ℝ := 2 * tau * Real.sqrt rho with hR_def
    have hrho_tau : rho ≤ tau * Real.sqrt rho := by
      calc
        rho = Real.sqrt rho * Real.sqrt rho := hsqrt_sq.symm
        _ ≤ tau * Real.sqrt rho := by gcongr
    have h6delta_le : 6 * delta ≤ (3 / 2 : ℝ) * tau * Real.sqrt rho := by
      calc
        6 * delta ≤ rho := h6delta_rho
        _ ≤ tau * Real.sqrt rho := hrho_tau
        _ ≤ (3 / 2 : ℝ) * tau * Real.sqrt rho := by linarith
    have hradius_le :
        6 * delta + tau * Real.sqrt rho / 2 ≤ R := by
      rw [hR_def]
      linarith
    have hloc3 : scalarProjection v E ⊆ Metric.closedBall center R :=
      hloc1.trans (Metric.closedBall_subset_closedBall hradius_le)
    have htau_le_one : tau ≤ 1 := by
      have hinner := abs_real_inner_le_norm direction v
      rw [hdir, hv] at hinner
      simpa [tau] using hinner
    have hR_ge_rho : rho ≤ R := by
      rw [hR_def]
      linarith [hrho_tau]
    have hsqrt_rho_half : Real.sqrt rho ≤ 1 / 2 := by
      have h := Real.sqrt_le_sqrt (show rho ≤ 1 / 4 by linarith)
      have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      norm_num [hsqrt_four] at h ⊢
      exact h
    have hR_le_one : R ≤ 1 := by
      rw [hR_def]
      nlinarith
    have h_upper1 : N ≤
        Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN (R / rho) alpha := by
      simpa [hN_def] using
        IsADSet1.externalCoveringNumber_le_of_subset_closedBall
          hAD Set.Subset.rfl hloc3 hR_ge_rho hR_le_one
    have hR_div_rho : R / rho = 2 * x := by
      rw [hR_def, hx_def]
      have h10 : Real.sqrt rho ≠ 0 := hsqrt_rho_pos.ne'
      have h11 : rho = Real.sqrt rho * Real.sqrt rho := hsqrt_sq.symm
      have h12 :
          (2 * tau * Real.sqrt rho) / rho =
            (2 * tau * Real.sqrt rho) /
              (Real.sqrt rho * Real.sqrt rho) := by
        apply congr_arg (fun y : ℝ => (2 * tau * Real.sqrt rho) / y) h11
      rw [h12]
      have h13 :
          (2 * tau * Real.sqrt rho) /
              (Real.sqrt rho * Real.sqrt rho) =
            (2 * tau) / Real.sqrt rho := by
        field_simp [h10]
      rw [h13]
      ring
    rw [hR_div_rho] at h_upper1
    have h2x :
        Kakeya.realRpowENN (2 * x) alpha ≤
          2 * Kakeya.realRpowENN x alpha := by
      simp only [Kakeya.realRpowENN]
      have h20 : Real.rpow (2 * x) alpha =
          Real.rpow 2 alpha * Real.rpow x alpha :=
        Real.mul_rpow (by norm_num) hx_nonneg
      have h21 : Real.rpow 2 alpha ≤ 2 := by
        have h22 : Real.rpow 2 alpha ≤ Real.rpow 2 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have h23 : Real.rpow 2 1 = 2 := by simp
        linarith
      have h25 : 0 ≤ Real.rpow 2 alpha := Real.rpow_nonneg (by norm_num) alpha
      have h26 :
          ENNReal.ofReal (Real.rpow 2 alpha) ≤ (2 : ENNReal) := by
        have h27 :
            ENNReal.ofReal (Real.rpow 2 alpha) ≤
              ENNReal.ofReal (2 : ℝ) :=
          ENNReal.ofReal_le_ofReal h21
        simpa using h27
      have h24 :
          ENNReal.ofReal (Real.rpow (2 * x) alpha) ≤
            (2 : ENNReal) * ENNReal.ofReal (Real.rpow x alpha) := by
        rw [h20, ENNReal.ofReal_mul h25]
        exact mul_le_mul_of_nonneg_right h26 (by simp)
      exact h24
    have h_upper2 : N ≤
        2 * Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN x alpha := by
      calc
        N ≤ Kakeya.realRpowENN delta (-epsilon) *
            Kakeya.realRpowENN (2 * x) alpha := h_upper1
        _ ≤ Kakeya.realRpowENN delta (-epsilon) *
            (2 * Kakeya.realRpowENN x alpha) := by gcongr
        _ = 2 * Kakeya.realRpowENN delta (-epsilon) *
            Kakeya.realRpowENN x alpha := by ring
    have hresult := h_cmp delta epsilon alpha x N 2
      hdelta hdelta_one hepsilon halpha halpha_lt_one hx_nonneg
      (by norm_num) h_lower3 h_upper2
    norm_num at hresult ⊢
    exact hresult

/--
Direction-component width bound for paper (6δ) carriers.

Same conclusion as `tube_segment_ad_direction_bound` but accepts a set in a
`6*delta`-thick tube segment, with a factor-`36` stronger mass lower bound.
-/
theorem paper_tube_segment_ad_direction_bound
    (h_lower : TubeSegmentProjectionCoveringLowerBoundStatement)
    (h_loc : TubeSegmentProjectionLocalizationStatement)
    (h_cmp : ADCoveringComparisonWithConstantStatement) :
    ∀ sigma eta : ℝ,
      0 < sigma → sigma < 1 → 0 < eta →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta rho start : ℝ,
            0 < delta → delta ≤ delta₀ →
            6 * delta ≤ rho → rho ≤ 1 / 4 →
            ∀ (base direction v : Point3),
              ‖direction‖ = 1 → ‖v‖ = 1 →
              ∀ E : Set Point3,
                MeasurableSet E →
                E ⊆ tubeSegmentCarrier (6 * delta) base direction start rho →
                ENNReal.ofReal
                    (36 * Real.rpow delta eta * delta ^ 2 *
                      Real.sqrt rho) ≤
                  MeasureTheory.volume E →
                IsADSet1 (scalarProjection v E) rho (1 - sigma)
                    (Kakeya.realRpowENN delta (-eta)) →
                  ENNReal.ofReal
                      (|inner ℝ direction v| / Real.sqrt rho) ≤
                    Kakeya.realRpowENN delta (-(3 * eta / sigma)) := by
  intro sigma eta hsigma hsigma1 heta
  rcases exists_delta_absorb_direction_power hsigma heta with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, habsorb⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta rho start hdelta hdelta_le h6delta_rho hrho_quarter
    base direction v hdir hv E hE_meas hE_sub hvol hAD
  set x : ℝ := |inner ℝ direction v| / Real.sqrt rho with hx_def
  have hx_nonneg : 0 ≤ x := by positivity
  have h_power_raw := paper_tube_segment_ad_direction_power
      h_lower h_loc h_cmp
      delta rho eta (1 - sigma) start
      hdelta h6delta_rho hrho_quarter
      heta (by linarith) (by linarith)
      base direction v hdir hv
      E hE_meas hE_sub hvol hAD
  have hexp : 1 - (1 - sigma) = sigma := by ring
  rw [hexp] at h_power_raw
  have h_convert :
      Kakeya.realRpowENN x sigma = (ENNReal.ofReal x) ^ sigma := by
    simp only [Kakeya.realRpowENN]
    have h' : (ENNReal.ofReal x) ^ sigma =
        ENNReal.ofReal (x ^ sigma) :=
      ENNReal.ofReal_rpow_of_nonneg hx_nonneg hsigma.le
    exact h'.symm
  rw [h_convert] at h_power_raw
  exact habsorb delta hdelta hdelta_le (ENNReal.ofReal x) h_power_raw

end Kakeya.Assouad

end
