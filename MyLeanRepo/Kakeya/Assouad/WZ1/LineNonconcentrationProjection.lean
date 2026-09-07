import MyLeanRepo.Kakeya.Assouad.WZ1.FiniteOSWOneStepIteration
import MyLeanRepo.Kakeya.Assouad.WZ1.LineNonconcentrationProjectionStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.ThinTubesExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma40Absorption

/-!
WZ1 Proposition 41: combine Lemmas 40 and 44 with the explicit OSW,
normalization, smoothing, unsmoothing, and parameter-absorption inputs.
-/

namespace Kakeya.Assouad

open MeasureTheory

/-- Helper: combine absorption bound with Lemma 40 conclusion in a small context. -/
lemma wz1_final_absorption_step
    {delta epsilon epsilon40 A C_absorb E c_final K_final : ℝ}
    {H : Finset (Point2 × Point2 × Point2)}
    (hdelta_pos : 0 < delta)
    (h_abs : C_absorb * Real.rpow delta E ≥ Real.rpow delta (epsilon / 2))
    (h_absorb_main :
      c_final ^ 5 / (A * K_final ^ 2) ≥ C_absorb * Real.rpow delta E)
    (hlemma40' :
      ENNReal.ofReal
          ((c_final ^ 5 / (A * K_final ^ 2)) *
            Real.rpow delta (epsilon40 - 1)) ≤
        ↑(Metric.externalCoveringNumber
          delta.toNNReal (wz1DotDifferenceSet H)))
    (hepsilon40 : epsilon40 = epsilon / 2) :
    Kakeya.realRpowENN delta (epsilon - 1) ≤
      ↑(Metric.externalCoveringNumber
        delta.toNNReal (wz1DotDifferenceSet H)) := by
  have h4 :
      c_final ^ 5 / (A * K_final ^ 2) ≥
        Real.rpow delta (epsilon / 2) :=
    le_trans h_abs h_absorb_main
  have h5 :
      Real.rpow delta (epsilon / 2) =
        Real.rpow delta (epsilon - epsilon40) := by
    congr 1 <;> simp [hepsilon40] <;> ring
  have h_main_ineq :
      c_final ^ 5 / (A * K_final ^ 2) ≥
        Real.rpow delta (epsilon - epsilon40) := by
    rw [h5] at h4
    exact h4
  exact
    (lemma40_exponent_upgrade_ennreal hdelta_pos h_main_ineq).trans
      hlemma40'

private lemma one_sub_eighth_nonneg {epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1) :
    0 ≤ 1 - epsilon / 8 := by
  linarith

private lemma one_sub_eighth_le_of_sixteenth_reached
    {epsilon exponent : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon)
    (hreach : 1 - epsilon / 16 ≤ exponent) :
    1 - epsilon / 8 ≤ exponent := by
  linarith

private lemma one_sub_eighth_le_one {epsilon : ℝ}
    (hepsilon_nonneg : 0 ≤ epsilon) :
    1 - epsilon / 8 ≤ 1 := by
  linarith

private lemma real_rpow_nonneg_of_pos {delta exponent : ℝ}
    (hdelta : 0 < delta) :
    0 ≤ Real.rpow delta exponent :=
  Real.rpow_nonneg hdelta.le exponent

private lemma rpow_neg_eighth_one_le
    {delta epsilon : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hepsilon_nonneg : 0 ≤ epsilon) :
    1 ≤ Real.rpow delta (-epsilon / 8) := by
  apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    hdelta_pos hdelta_one
  linarith

private lemma final_thin_tube_constant_one_le
    {K factor : ℝ} (hK : 1 ≤ K) (hfactor : 1 ≤ factor) :
    1 ≤ (2 * (20 * K)) * factor := by
  have hbase : 1 ≤ 2 * (20 * K) := by nlinarith
  exact hbase.trans
    (le_mul_of_one_le_right (by linarith) hfactor)

private lemma frostman_constant_le_final
    {delta epsilon lambda K_N K_init K_final : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_one : delta ≤ 1)
    (hepsilon_nonneg : 0 ≤ epsilon) (hlambda_nonneg : 0 ≤ lambda)
    (hK_N_ge_init : K_init ≤ K_N)
    (hK_init_eq :
      K_init = 200 * Real.rpow delta (-3 * lambda / 2))
    (hK_final_eq :
      K_final =
        (2 * (20 * K_N)) * Real.rpow delta (-epsilon / 8)) :
    Kakeya.realRpowENN delta (-lambda) ≤ ENNReal.ofReal K_final := by
  have hfactor_nonneg : 0 ≤ Real.rpow delta (-epsilon / 8) :=
    Real.rpow_nonneg hdelta_pos.le _
  have hbase :
      40 * K_init * Real.rpow delta (-epsilon / 8) ≤ K_final := by
    rw [hK_final_eq]
    have hscale : 40 * K_init ≤ 2 * (20 * K_N) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hscale hfactor_nonneg
  have hproduct :
      40 * K_init * Real.rpow delta (-epsilon / 8) =
        8000 * Real.rpow delta
          (-3 * lambda / 2 - epsilon / 8) := by
    rw [hK_init_eq]
    calc
      40 * (200 * Real.rpow delta (-3 * lambda / 2)) *
            Real.rpow delta (-epsilon / 8)
          = 8000 *
              (Real.rpow delta (-3 * lambda / 2) *
                Real.rpow delta (-epsilon / 8)) := by ring
      _ = 8000 *
            Real.rpow delta
              ((-3 * lambda / 2) + (-epsilon / 8)) := by
            exact congrArg (fun x : ℝ => 8000 * x)
              (Real.rpow_add hdelta_pos
                (-3 * lambda / 2) (-epsilon / 8)).symm
      _ = 8000 *
            Real.rpow delta
              (-3 * lambda / 2 - epsilon / 8) := by ring_nf
  have hexponent :
      -3 * lambda / 2 - epsilon / 8 ≤ -lambda := by
    linarith
  have hrpow :
      Real.rpow delta (-lambda) ≤
        Real.rpow delta (-3 * lambda / 2 - epsilon / 8) :=
    Real.rpow_le_rpow_of_exponent_ge
      hdelta_pos hdelta_one hexponent
  have hreal : Real.rpow delta (-lambda) ≤ K_final := by
    calc
      Real.rpow delta (-lambda)
          ≤ Real.rpow delta
              (-3 * lambda / 2 - epsilon / 8) := hrpow
      _ ≤ 8000 *
            Real.rpow delta
              (-3 * lambda / 2 - epsilon / 8) := by
        exact le_mul_of_one_le_left
          (Real.rpow_nonneg hdelta_pos.le _) (by norm_num)
      _ = 40 * K_init * Real.rpow delta (-epsilon / 8) :=
        hproduct.symm
      _ ≤ K_final := hbase
  simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono hreal

private lemma final_exceptional_parameter_bounds
    {delta alpha alpha' c₀ c_final : ℝ} {N : ℕ}
    (hdelta_pos : 0 < delta)
    (halpha' : alpha' = 2 * alpha)
    (hc₀ : c₀ = Real.rpow delta alpha')
    (hc_final : c_final = 2 * ((3 : ℝ)^N * c₀))
    (hsmall :
      2 * (3 : ℝ)^N * Real.rpow delta (2 * alpha) < 1)
    (hdensity :
      4 * (3 : ℝ)^N * Real.rpow delta alpha ≤ 1) :
    0 ≤ c_final ∧ c_final < 1 ∧
      2 * c_final ≤ Real.rpow delta alpha := by
  have hrpow_nonneg : 0 ≤ Real.rpow delta alpha :=
    Real.rpow_nonneg hdelta_pos.le _
  have hrpow_two :
      Real.rpow delta (2 * alpha) =
        Real.rpow delta alpha * Real.rpow delta alpha := by
    rw [show 2 * alpha = alpha + alpha by ring]
    exact Real.rpow_add hdelta_pos alpha alpha
  have hc_final_rpow :
      c_final =
        2 * (3 : ℝ)^N * Real.rpow delta (2 * alpha) := by
    rw [hc_final, hc₀, halpha']
    ring
  have hc_final_nonneg : 0 ≤ c_final := by
    rw [hc_final_rpow]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (by positivity))
      (Real.rpow_nonneg hdelta_pos.le _)
  have hc_final_lt_one : c_final < 1 := by
    rw [hc_final_rpow]
    exact hsmall
  have hdensity_final :
      2 * c_final ≤ Real.rpow delta alpha := by
    rw [hc_final_rpow, hrpow_two]
    calc
      2 * (2 * (3 : ℝ)^N *
          (Real.rpow delta alpha * Real.rpow delta alpha))
          = (4 * (3 : ℝ)^N * Real.rpow delta alpha) *
              Real.rpow delta alpha := by ring
      _ ≤ 1 * Real.rpow delta alpha :=
        mul_le_mul_of_nonneg_right hdensity hrpow_nonneg
      _ = Real.rpow delta alpha := one_mul _
  exact ⟨hc_final_nonneg, hc_final_lt_one, hdensity_final⟩

private lemma ofReal_two_mul_le_realRpowENN
    {delta alpha c : ℝ}
    (h : 2 * c ≤ Real.rpow delta alpha) :
    ENNReal.ofReal (2 * c) ≤ Kakeya.realRpowENN delta alpha := by
  simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono h

private lemma final_constant_bound_from_iterated_bound
    {delta epsilon K_N D exponent : ℝ}
    (hdelta_pos : 0 < delta)
    (hK : K_N ≤ D * Real.rpow delta exponent) :
    (2 * (20 * K_N)) * Real.rpow delta (-epsilon / 8) ≤
      40 * D * Real.rpow delta (exponent - epsilon / 8) := by
  have hfactor_nonneg : 0 ≤ Real.rpow delta (-epsilon / 8) :=
    Real.rpow_nonneg hdelta_pos.le _
  have hscaled :
      40 * K_N * Real.rpow delta (-epsilon / 8) ≤
        40 * (D * Real.rpow delta exponent) *
          Real.rpow delta (-epsilon / 8) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK (by norm_num)) hfactor_nonneg
  have hrpow :
      Real.rpow delta exponent * Real.rpow delta (-epsilon / 8) =
        Real.rpow delta (exponent - epsilon / 8) := by
    rw [show exponent - epsilon / 8 =
      exponent + (-epsilon / 8) by ring]
    exact (Real.rpow_add hdelta_pos exponent (-epsilon / 8)).symm
  calc
    (2 * (20 * K_N)) * Real.rpow delta (-epsilon / 8)
        = 40 * K_N * Real.rpow delta (-epsilon / 8) := by ring
    _ ≤ 40 * (D * Real.rpow delta exponent) *
          Real.rpow delta (-epsilon / 8) := hscaled
    _ = 40 * D *
          (Real.rpow delta exponent *
            Real.rpow delta (-epsilon / 8)) := by ring
    _ = 40 * D * Real.rpow delta (exponent - epsilon / 8) := by
      rw [hrpow]

private lemma wz1_line_nonconcentration_projection_for_zeta
    (h_lemma44 : WZ1QuarterThinTubesStatement)
    (h_lemma40 : WZ1ThinTubesLargeDotProductStatement)
    (h_norm : WZ1OSWSupportNormalizationStatement)
    (h_transport : WZ1OSWCommonSimilarityTransportStatement)
    (h_d2s : WZ1DiscreteToSmoothedThinTubesStatement)
    (h_frostman : WZ1SharpSmoothedFrostmanStatement)
    (h_s2d : WZ1SmoothedToDiscreteThinTubesStatement)
    {epsilon tau M lambda : ℝ} {N : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (htau : 0 < tau) (hM : 1 ≤ M)
    (hstep :
      ∀ (N : ℕ) (sigma c K C : ℝ)
        (nu₁ nu₂ : ProbabilityMeasure Point2),
        (nu₁ : Measure Point2).support ⊆ Metric.closedBall 0 1 →
        (nu₂ : Measure Point2).support ⊆ Metric.closedBall 0 1 →
        (∀ n : ℕ, n < N →
          sigma + (n : ℝ) * tau ∈
            Set.Icc (1 / 4 : ℝ) (1 - epsilon / 16)) →
        (∀ n : ℕ, n < N →
          (3 : ℝ) ^ n * c ∈ Set.Ioo (0 : ℝ) (1 / 10)) →
        1 ≤ K →
        1 ≤ C →
        (1 : ℝ) / 2 ≤
          sInf {d : ℝ |
            ∃ x ∈ (nu₁ : Measure Point2).support,
              ∃ y ∈ (nu₂ : Measure Point2).support,
                dist x y = d} →
        (∀ (x : Point2) (r : ℝ), 0 < r →
          nu₁ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
        (∀ (x : Point2) (r : ℝ), 0 < r →
          nu₂ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
        HasMeasureThinTubes sigma K c nu₁ nu₂ →
        HasMeasureThinTubes sigma K c nu₂ nu₁ →
          HasMeasureThinTubes
              (sigma + (N : ℝ) * tau)
              (wz1_one_step_iterated_K N K C M c)
              ((3 : ℝ) ^ N * c) nu₁ nu₂ ∧
            HasMeasureThinTubes
              (sigma + (N : ℝ) * tau)
              (wz1_one_step_iterated_K N K C M c)
              ((3 : ℝ) ^ N * c) nu₂ nu₁)
    (hreach :
      1 - epsilon / 16 ≤ (1 / 4 : ℝ) + (N : ℝ) * tau)
    (hstrict :
      ∀ n : ℕ, n < N →
        (1 / 4 : ℝ) + (n : ℝ) * tau < 1 - epsilon / 16)
    (hlambda : lambda = epsilon / (100 * M ^ N))
    (hlambda_pos : 0 < lambda)
    (hMN_one : 1 ≤ (M ^ N : ℝ)) :
    ∀ zeta : ℝ, 0 < zeta → zeta < 1 →
      ∃ alpha delta₀ : ℝ,
        0 < alpha ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F G₁ G₂ : DiscreteSet 2,
            F.Nonempty → G₁.Nonempty → G₂.Nonempty →
            F.IsInUnitBall →
            G₁.IsInUnitBall →
            G₂.IsInUnitBall →
            F.IsDeltaSeparated delta →
            G₁.IsDeltaSeparated delta →
            G₂.IsDeltaSeparated delta →
            F.IsFrostman delta 1
              (Kakeya.realRpowENN delta (-lambda)) →
            G₁.IsFrostman delta 1
              (Kakeya.realRpowENN delta (-lambda)) →
            G₂.IsFrostman delta 1
              (Kakeya.realRpowENN delta (-lambda)) →
            WZ1StandardSeparation F G₁ G₂ →
            WZ1LineNonConcentration delta lambda zeta G₁ →
            WZ1LineNonConcentration delta lambda zeta G₂ →
              ∀ H : Finset (Point2 × Point2 × Point2),
                WZ1UniformTripleDensity
                    (Kakeya.realRpowENN delta alpha)
                    F G₁ G₂ H →
                  Kakeya.realRpowENN delta (epsilon - 1) ≤
                    (↑(Metric.externalCoveringNumber
                      (Real.toNNReal delta)
                      (wz1DotDifferenceSet H)) : ENNReal) := by
  intro zeta hzeta_pos hzeta_lt_one

  set alpha : ℝ := zeta * lambda / 12 with halpha
  set alpha' : ℝ := 2 * alpha with halpha'
  have halpha_pos : 0 < alpha := by positivity
  have halpha'_pos : 0 < alpha' := by positivity
  have halpha'_eq : alpha' = zeta * lambda / 6 := by
    dsimp only [alpha', alpha] <;> ring

  set epsilon40 : ℝ := epsilon / 2 with hepsilon40
  have hepsilon40_pos : 0 < epsilon40 := by positivity
  rcases h_lemma40 epsilon40 hepsilon40_pos with
    ⟨A, hA_one, delta₀_40, hdelta₀_40_pos, hdelta₀_40_one, hlemma40⟩

  set D_const : ℝ := max 1 (max (200 : ℝ) (200^2 * M)) with hD_const
  set e_max : ℝ := 2 * lambda + alpha' with he_max
  have hD_const_one : 1 ≤ D_const := le_max_left _ _
  have hD_const_pos : 0 < D_const := by linarith

  have h1 : alpha' < lambda / 6 := by
    rw [halpha'_eq]
    have hmul : zeta * lambda < lambda := by
      have h : zeta * lambda < 1 * lambda :=
        mul_lt_mul_of_pos_right hzeta_lt_one hlambda_pos
      simpa using h
    have h7 : (zeta * lambda) / 6 < lambda / 6 := by
      apply div_lt_div_of_pos_right hmul
      norm_num
    exact h7
  set E : ℝ :=
    5 * alpha' + 2 * (M^N : ℝ) * e_max + epsilon / 4 with hE
  have hE_lt_half : E < epsilon / 2 := by
    have h2 : 5 * alpha' < (5 / 6 : ℝ) * lambda := by
      have h22 : 5 * alpha' < 5 * (lambda / 6) :=
        mul_lt_mul_of_pos_left h1 (by norm_num)
      have h23 : 5 * (lambda / 6) = (5 / 6 : ℝ) * lambda := by ring
      rw [h23] at h22
      exact h22
    have h4 : 2 * lambda + alpha' < (13 / 6 : ℝ) * lambda := by
      have h41 : 2 * lambda + alpha' < 2 * lambda + lambda / 6 :=
        add_lt_add_right h1 (2 * lambda)
      have h42 :
          2 * lambda + lambda / 6 = (13 / 6 : ℝ) * lambda := by
        ring
      rw [h42] at h41
      exact h41
    have h5 : 0 < 2 * (M^N : ℝ) := by positivity
    have h3 :
        2 * (M^N : ℝ) * (2 * lambda + alpha') <
          2 * (M^N : ℝ) * ((13 / 6 : ℝ) * lambda) :=
      mul_lt_mul_of_pos_left h4 h5
    have h7 :
        2 * (M^N : ℝ) * ((13 / 6 : ℝ) * lambda) =
          (13 / 3 : ℝ) * (M^N : ℝ) * lambda := by
      ring
    rw [h7] at h3
    have hE1 :
        E < (5 / 6 : ℝ) * lambda +
          (13 / 3 : ℝ) * (M^N : ℝ) * lambda + epsilon / 4 := by
      dsimp only [E, e_max]
      linarith
    have hlam : lambda = epsilon / (100 * (M^N : ℝ)) := by
      simp [hlambda]
    rw [hlam] at hE1
    have hMN_ne_zero : (M^N : ℝ) ≠ 0 := by linarith
    have h12 :
        (13 / 3 : ℝ) * (M^N : ℝ) *
            (epsilon / (100 * (M^N : ℝ))) =
          (13 : ℝ) * epsilon / 300 := by
      field_simp [hMN_ne_zero] <;> ring
    have h9 :
        (5 / 6 : ℝ) * (epsilon / (100 * (M^N : ℝ))) ≤
          epsilon / 120 := by
      have h11 :
          epsilon / (100 * (M^N : ℝ)) ≤ epsilon / 100 := by
        apply div_le_div_of_nonneg_left (by linarith) (by positivity)
        nlinarith
      nlinarith
    rw [h12] at hE1
    linarith

  set C_absorb : ℝ :=
    (32 * (3 : ℝ)^(5 * N)) /
      (A * 1600 * D_const^(2*M^N)) with hC_absorb
  have hC_absorb_pos : 0 < C_absorb := by positivity
  rcases exists_delta_const_mul_rpow_ge_rpow
      hC_absorb_pos hE_lt_half with
    ⟨delta₀_abs, hdelta₀_abs_pos, hdelta₀_abs_one, hbound_abs⟩
  rcases exists_delta_exceptional_bound N alpha halpha_pos with
    ⟨delta₀_exc, hdelta₀_exc_pos, hdelta₀_exc_one, hbound_exc⟩
  rcases h_lemma44 lambda zeta alpha'
      hlambda_pos hzeta_pos halpha'_pos with
    ⟨delta₀_44, hdelta₀_44_pos, hdelta₀_44_one, h44_inner⟩

  let delta₀ : ℝ :=
    min delta₀_44
      (min (1 / 10) (min delta₀_exc (min delta₀_40 delta₀_abs)))
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 :=
    le_trans (min_le_left _ _) hdelta₀_44_one
  refine ⟨alpha, delta₀, halpha_pos, hdelta₀_pos, hdelta₀_one, ?_⟩

  intro delta hdelta_pos hdelta_le F G₁ G₂
    hF_nonempty hG1_nonempty hG2_nonempty
    hF_unit hG1_unit hG2_unit hF_sep hG1_sep hG2_sep
    hF_frost hG1_frost hG2_frost hstd_sep h_nc1 h_nc2 H hdensity
  have h_le_44 : delta ≤ delta₀_44 :=
    le_trans hdelta_le (min_le_left _ _)
  have h_le_one_tenth : delta ≤ 1 / 10 :=
    le_trans hdelta_le
      (min_le_right _ _ |>.trans (min_le_left _ _))
  have h_le_exc : delta ≤ delta₀_exc :=
    le_trans hdelta_le
      (min_le_right _ _ |>.trans
        (min_le_right _ _ |>.trans (min_le_left _ _)))
  have h_le_40 : delta ≤ delta₀_40 :=
    le_trans hdelta_le
      (min_le_right _ _ |>.trans
        (min_le_right _ _ |>.trans
          (min_le_right _ _ |>.trans (min_le_left _ _))))
  have h_le_abs : delta ≤ delta₀_abs :=
    le_trans hdelta_le
      (min_le_right _ _ |>.trans
        (min_le_right _ _ |>.trans
          (min_le_right _ _ |>.trans (min_le_right _ _))))
  have h_exc := hbound_exc delta hdelta_pos h_le_exc

  have h_diam1 : ∀ x ∈ G₁, ∀ y ∈ G₁, dist x y ≤ 1 / 10 :=
    hstd_sep.2.1
  have h_diam2 : ∀ x ∈ G₂, ∀ y ∈ G₂, dist x y ≤ 1 / 10 :=
    hstd_sep.2.2.1
  have h_mutual_sep : WZ1MutuallySeparated G₁ G₂ (1 / 2) :=
    hstd_sep.2.2.2.1
  have h_mutual_sep_symm : WZ1MutuallySeparated G₂ G₁ (1 / 2) := by
    intro x hx y hy
    simpa [dist_comm] using h_mutual_sep y hy x hx

  have hthin44_12 :
      HasDiscreteThinTubes delta (1 / 4)
        (Real.rpow delta (-3 * alpha' / zeta - lambda))
        (Real.rpow delta alpha') G₁ G₂ :=
    h44_inner delta hdelta_pos h_le_44 G₁ G₂
      hG1_nonempty hG2_nonempty hG1_unit hG2_unit
      hG1_sep hG2_sep hG1_frost hG2_frost h_mutual_sep h_nc2
  have hthin44_21 :
      HasDiscreteThinTubes delta (1 / 4)
        (Real.rpow delta (-3 * alpha' / zeta - lambda))
        (Real.rpow delta alpha') G₂ G₁ :=
    h44_inner delta hdelta_pos h_le_44 G₂ G₁
      hG2_nonempty hG1_nonempty hG2_unit hG1_unit
      hG2_sep hG1_sep hG2_frost hG1_frost h_mutual_sep_symm h_nc1
  have hK0_exp :
      -3 * alpha' / zeta - lambda = -3 * lambda / 2 := by
    rw [halpha'_eq]
    field_simp [hzeta_pos.ne] <;> ring
  let K₀ : ℝ := Real.rpow delta (-3 * lambda / 2)
  let c₀ : ℝ := Real.rpow delta alpha'
  have hK0_eq :
      Real.rpow delta (-3 * alpha' / zeta - lambda) = K₀ := by
    rw [hK0_exp]
  have hthin44_12' :
      HasDiscreteThinTubes delta (1 / 4) K₀ c₀ G₁ G₂ := by
    rwa [hK0_eq] at hthin44_12
  have hthin44_21' :
      HasDiscreteThinTubes delta (1 / 4) K₀ c₀ G₂ G₁ := by
    rwa [hK0_eq] at hthin44_21

  rcases h_norm G₁ G₂ hG1_nonempty hG2_nonempty
      hdelta_pos h_le_one_tenth hG1_sep hG2_sep hG1_unit hG2_unit
      h_diam1 h_diam2 h_mutual_sep with
    ⟨D⟩
  let C_frost : ENNReal := Kakeya.realRpowENN delta (-lambda)
  have h_rpow_lambda_one : 1 ≤ Real.rpow delta (-lambda) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta_pos (h_le_one_tenth.trans (by norm_num)) (by linarith)
  have hC_frost_one : 1 ≤ C_frost := by
    simpa [C_frost, Kakeya.realRpowENN] using
      ENNReal.one_le_ofReal.mpr h_rpow_lambda_one
  rcases h_transport D hC_frost_one hG1_frost hG2_frost with
    ⟨T⟩
  have hthin_norm_12 :
      HasDiscreteThinTubes D.normalizedDelta (1 / 4) (2 * K₀) c₀
        D.normalized₁ D.normalized₂ :=
    T.thin_forward₁₂ (by norm_num) hthin44_12'
  have hthin_norm_21 :
      HasDiscreteThinTubes D.normalizedDelta (1 / 4) (2 * K₀) c₀
        D.normalized₂ D.normalized₁ :=
    T.thin_forward₂₁ (by norm_num) hthin44_21'

  have hnd10_pos : 0 < D.normalizedDelta / 10 :=
    div_pos D.normalizedDelta_pos (by norm_num)
  let nu₁ := smoothMeasure D.normalized₁ D.normalized₁_nonempty
    (D.normalizedDelta / 10) hnd10_pos
  let nu₂ := smoothMeasure D.normalized₂ D.normalized₂_nonempty
    (D.normalizedDelta / 10) hnd10_pos
  have hthin_meas_12 :
      HasMeasureThinTubes (1 / 4) (100 * (2 * K₀)) c₀ nu₁ nu₂ :=
    h_d2s D.normalized₁ D.normalized₂
      D.normalized₁_nonempty D.normalized₂_nonempty
      D.normalizedDelta_pos (by norm_num)
      D.normalized₁_separated D.normalized₂_separated hthin_norm_12
  have hthin_meas_21 :
      HasMeasureThinTubes (1 / 4) (100 * (2 * K₀)) c₀ nu₂ nu₁ :=
    h_d2s D.normalized₂ D.normalized₁
      D.normalized₂_nonempty D.normalized₁_nonempty
      D.normalizedDelta_pos (by norm_num)
      D.normalized₂_separated D.normalized₁_separated hthin_norm_21

  let C_real : ℝ := 2 * Real.rpow delta (-lambda)
  have hC_real_one : 1 ≤ C_real := by
    dsimp only [C_real]
    linarith
  have hC_frost_eq :
      (2 * C_frost : ENNReal) = ENNReal.ofReal C_real := by
    simp [C_frost, Kakeya.realRpowENN, C_real]
  have hfrost1_real :
      D.normalized₁.IsFrostman D.normalizedDelta 1
        (ENNReal.ofReal C_real) := by
    simpa [hC_frost_eq] using T.normalized₁_frostman
  have hfrost2_real :
      D.normalized₂.IsFrostman D.normalizedDelta 1
        (ENNReal.ofReal C_real) := by
    simpa [hC_frost_eq] using T.normalized₂_frostman
  have hnd_one : D.normalizedDelta ≤ 1 :=
    D.normalizedDelta_upper.trans (by norm_num)
  have hball1 :
      ∀ (x : Point2) (r : ℝ), 0 < r →
        nu₁ (Metric.ball x r) ≤ Real.toNNReal (100 * C_real * r) :=
    h_frostman D.normalized₁ D.normalized₁_nonempty
      D.normalizedDelta_pos hnd_one hC_real_one
      D.normalized₁_separated hfrost1_real
  have hball2 :
      ∀ (x : Point2) (r : ℝ), 0 < r →
        nu₂ (Metric.ball x r) ≤ Real.toNNReal (100 * C_real * r) :=
    h_frostman D.normalized₂ D.normalized₂_nonempty
      D.normalizedDelta_pos hnd_one hC_real_one
      D.normalized₂_separated hfrost2_real

  let K_init : ℝ := 100 * (2 * K₀)
  let C_osw : ℝ := 100 * C_real
  have hK_init_eq :
      K_init = 200 * Real.rpow delta (-3 * lambda / 2) := by
    dsimp only [K_init, K₀]
    ring
  have hC_osw_eq :
      C_osw = 200 * Real.rpow delta (-lambda) := by
    dsimp only [C_osw, C_real]
    ring
  have hK_init_one : 1 ≤ K_init := by
    rw [hK_init_eq]
    have hpow :
        1 ≤ Real.rpow delta (-3 * lambda / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta_pos (h_le_one_tenth.trans (by norm_num)) (by linarith)
    nlinarith
  have hC_osw_one : 1 ≤ C_osw := by
    rw [hC_osw_eq]
    have h2 : -lambda ≤ 0 := by linarith
    have h3 : Real.rpow delta (-lambda) ≥ Real.rpow delta 0 :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos (by linarith) h2
    have h4 : Real.rpow delta 0 = (1 : ℝ) := by simp
    have h5 : (1 : ℝ) ≤ Real.rpow delta (-lambda) := by
      rw [h4] at h3
      exact h3
    have h6 : (1 : ℝ) ≤ 200 * Real.rpow delta (-lambda) := by
      calc
        (1 : ℝ) ≤ 200 := by norm_num
        _ ≤ 200 * Real.rpow delta (-lambda) :=
          le_mul_of_one_le_right (by norm_num) h5
    exact h6

  have hsigma_range :
      ∀ n : ℕ, n < N →
        (1 / 4 : ℝ) + (n : ℝ) * tau ∈
          Set.Icc (1 / 4) (1 - epsilon / 16) := by
    intro n hn
    have h_lower :
        (1 / 4 : ℝ) ≤ (1 / 4 : ℝ) + (n : ℝ) * tau := by
      have h : 0 ≤ (n : ℝ) * tau := by positivity
      linarith
    exact ⟨h_lower, (hstrict n hn).le⟩
  have hc_range :
      ∀ n : ℕ, n < N →
        (3 : ℝ)^n * c₀ ∈ Set.Ioo (0 : ℝ) (1 / 10) := by
    intro n hn
    have h_pos : 0 < (3 : ℝ)^n * c₀ := by
      apply mul_pos
      · positivity
      · dsimp only [c₀]
        exact Real.rpow_pos_of_pos hdelta_pos _
    have h_n_le : n ≤ N := by linarith
    have h3n_le : (3 : ℝ)^n ≤ (3 : ℝ)^N := by
      gcongr <;> norm_num
    have hc0_nonneg : 0 ≤ c₀ := by
      dsimp only [c₀]
      exact Real.rpow_nonneg hdelta_pos.le _
    have hupper : (3 : ℝ)^N * c₀ < 1 / 10 := by
      have h6 : c₀ = Real.rpow delta alpha' := by rfl
      have h7 : alpha' = 2 * alpha := by
        dsimp only [alpha', alpha] <;> ring
      rw [h6, h7]
      exact h_exc.1
    exact
      ⟨h_pos,
        (mul_le_mul_of_nonneg_right h3n_le hc0_nonneg).trans_lt
          hupper⟩
  rcases hstep N (1 / 4) c₀ K_init C_osw nu₁ nu₂
      D.smooth₁_support D.smooth₂_support
      hsigma_range hc_range hK_init_one hC_osw_one
      D.smooth_mutual_distance hball1 hball2
      hthin_meas_12 hthin_meas_21 with
    ⟨hthin_osw_12, _hthin_osw_21⟩

  let K_N : ℝ := wz1_one_step_iterated_K N K_init C_osw M c₀
  have hK_N_bound :
      K_N ≤
        Real.rpow D_const (M ^ N) *
          Real.rpow delta (-(M ^ N : ℝ) * e_max) := by
    dsimp only [K_N]
    have hmax_eq :
        max (3 * lambda / 2) (2 * lambda + alpha') = e_max := by
      exact (max_eq_right (by linarith [halpha'_pos])).trans he_max.symm
    have h_bound := wz1_one_step_iterated_K_bound N
      hdelta_pos (h_le_one_tenth.trans (by norm_num)) hM hK_init_one
      (show 0 ≤ C_osw by linarith)
      (show (0 : ℝ) < 200 by norm_num)
      (show (0 : ℝ) < 200 by norm_num)
      (show 0 ≤ 3 * lambda / 2 by positivity)
      (show 0 ≤ lambda by positivity)
      (show 0 ≤ alpha' by positivity)
      (by
        have h_exp : -3 * lambda / 2 = -(3 * lambda / 2) := by ring
        rw [hK_init_eq, h_exp])
      (by rw [hC_osw_eq])
      (le_refl (Real.rpow delta alpha'))
    rw [hmax_eq] at h_bound
    have hD_eq :
        D_const = max 1 (max (200 : ℝ) (200 ^ 2 * M)) :=
      hD_const
    rw [hD_eq]
    exact h_bound

  let beta_target : ℝ := 1 - epsilon / 8
  have hbeta_target_pos : 0 ≤ beta_target := by
    simpa [beta_target] using
      one_sub_eighth_nonneg hepsilon_pos hepsilon_lt_one
  have hbeta_target_le :
      beta_target ≤ (1 / 4 : ℝ) + (N : ℝ) * tau := by
    apply one_sub_eighth_le_of_sixteenth_reached hepsilon_pos.le
    exact hreach
  have hthin_mono_12 :
      HasMeasureThinTubes beta_target K_N
        ((3 : ℝ)^N * c₀) nu₁ nu₂ :=
    hthin_osw_12.mono_exponent hbeta_target_pos hbeta_target_le

  have h2c_lt_one : 2 * ((3 : ℝ)^N * c₀) < 1 := by
    have h1 :
        2 * (3 : ℝ)^N * Real.rpow delta (2 * alpha) < 1 :=
      h_exc.2.1
    have h2 : c₀ = Real.rpow delta alpha' := by rfl
    have h3 : alpha' = 2 * alpha := by
      dsimp only [alpha', alpha] <;> ring
    have h4 :
        2 * ((3 : ℝ)^N * c₀) =
          2 * (3 : ℝ)^N * Real.rpow delta (2 * alpha) := by
      rw [h2, h3]
      ring
    rw [h4]
    exact h1
  have hbeta_target_le_one : beta_target ≤ 1 := by
    simpa [beta_target] using one_sub_eighth_le_one hepsilon_pos.le
  have hc0_nonneg : 0 ≤ c₀ := by
    dsimp only [c₀]
    exact Real.rpow_nonneg hdelta_pos.le _
  have hc_meas_nonneg : 0 ≤ (3 : ℝ)^N * c₀ := by
    exact mul_nonneg (by positivity) hc0_nonneg
  have hthin_disc_12 :
      HasDiscreteThinTubes D.normalizedDelta beta_target
        (20 * K_N) (2 * ((3 : ℝ)^N * c₀))
        D.normalized₁ D.normalized₂ :=
    h_s2d D.normalized₁ D.normalized₂
      D.normalized₁_nonempty D.normalized₂_nonempty
      D.normalizedDelta_pos hbeta_target_le_one
      hc_meas_nonneg h2c_lt_one hthin_mono_12
  have hthin_back_12 :
      HasDiscreteThinTubes delta beta_target
        (2 * (20 * K_N)) (2 * ((3 : ℝ)^N * c₀)) G₁ G₂ :=
    T.thin_backward₁₂ hbeta_target_le_one hthin_disc_12

  let c_final : ℝ := 2 * ((3 : ℝ)^N * c₀)
  let K_final : ℝ :=
    (2 * (20 * K_N)) * delta ^ (-(epsilon / 8))
  have hK_final_rpow :
      K_final =
        (2 * (20 * K_N)) * Real.rpow delta (-epsilon / 8) := by
    have h_exp : (-(epsilon / 8)) = -epsilon / 8 := by ring
    have h_pow :
        delta ^ (-(epsilon / 8)) =
          Real.rpow delta (-epsilon / 8) := by
      rw [h_exp] <;> rfl
    dsimp only [K_final]
    rw [h_pow] <;> ring
  have hdelta_one : delta ≤ 1 :=
    h_le_one_tenth.trans (by norm_num)
  have h_rpow_eps8_one :
      1 ≤ Real.rpow delta (-epsilon / 8) :=
    rpow_neg_eighth_one_le hdelta_pos hdelta_one hepsilon_pos.le
  have hthin_final :
      HasDiscreteThinTubes delta 1 K_final c_final G₁ G₂ :=
    HasDiscreteThinTubes.to_exponent_one (epsilon := epsilon / 8)
      hthin_back_12 hdelta_pos hdelta_one
      (by positivity) (by rfl) hbeta_target_le_one
  have hK_final_one : 1 ≤ K_final := by
    rw [hK_final_rpow]
    exact final_thin_tube_constant_one_le
      (wz1_one_step_iterated_K_one_le N hK_init_one hM)
      h_rpow_eps8_one
  have hK_N_ge_init : K_init ≤ K_N :=
    wz1_one_step_iterated_K_mono N hK_init_one hM
  have h_frost_weak :
      Kakeya.realRpowENN delta (-lambda) ≤ ENNReal.ofReal K_final :=
    frostman_constant_le_final
      hdelta_pos hdelta_one hepsilon_pos.le hlambda_pos.le
      hK_N_ge_init hK_init_eq hK_final_rpow
  have hF_frost' :
      F.IsFrostman delta 1 (ENNReal.ofReal K_final) :=
    hF_frost.mono_const h_frost_weak
  have hG1_frost' :
      G₁.IsFrostman delta 1 (ENNReal.ofReal K_final) :=
    hG1_frost.mono_const h_frost_weak
  have hG2_frost' :
      G₂.IsFrostman delta 1 (ENNReal.ofReal K_final) :=
    hG2_frost.mono_const h_frost_weak

  have h_exceptional_bounds :
      0 ≤ c_final ∧ c_final < 1 ∧
        2 * c_final ≤ Real.rpow delta alpha := by
    exact final_exceptional_parameter_bounds
      hdelta_pos halpha' rfl rfl h_exc.2.1 h_exc.2.2
  have hdensity' :
      WZ1UniformTripleDensity
        (ENNReal.ofReal (2 * c_final)) F G₁ G₂ H :=
    uniform_triple_density_mono hdensity
      (ofReal_two_mul_le_realRpowENN h_exceptional_bounds.2.2)
  have hlemma40' := hlemma40 delta hdelta_pos h_le_40 c_final K_final
    h_exceptional_bounds.1 h_exceptional_bounds.2.1 hK_final_one
    F G₁ G₂ hF_nonempty hG1_nonempty hG2_nonempty
    hF_unit hG1_unit hG2_unit hF_sep hG1_sep hG2_sep
    hF_frost' hG1_frost' hG2_frost' hstd_sep
    hthin_final H hdensity'

  have hK_final_bound :
      K_final ≤
        40 * D_const ^ (M ^ N) *
          Real.rpow delta (-(M ^ N : ℝ) * e_max - epsilon / 8) := by
    rw [hK_final_rpow]
    exact final_constant_bound_from_iterated_bound
      hdelta_pos hK_N_bound
  have h_absorb_main :
      c_final ^ 5 / (A * K_final ^ 2) ≥
        C_absorb * Real.rpow delta E := by
    let Dpow : ℝ := D_const ^ (M ^ N)
    have hDpow_pos : 0 < Dpow := by positivity
    have hDpow_sq :
        Dpow ^ 2 = D_const ^ (2 * M ^ N) := by
      dsimp only [Dpow]
      rw [pow_two, ← Real.rpow_add hD_const_pos]
      congr 1
      ring
    have hC_absorb' :
        C_absorb =
          32 * (3 : ℝ) ^ (5 * N) /
            (A * 1600 * Dpow ^ 2) := by
      rw [hC_absorb, hDpow_sq]
    have hmain := wz1_absorption_algebra
      (N := N) (alpha' := alpha') (epsilon := epsilon)
      (M := M) (e_max := e_max) (A := A)
      hdelta_pos rfl hK_final_one
      (by simpa [Dpow] using hK_final_bound)
      hC_absorb' hE hA_one hDpow_pos halpha'_pos hepsilon_pos
    simpa [c_final, c₀, mul_assoc] using hmain
  exact wz1_final_absorption_step hdelta_pos
    (hbound_abs delta hdelta_pos h_le_abs)
    h_absorb_main hlemma40' (by simp [epsilon40])

theorem wz1_line_nonconcentration_projection :
    WZ1LineNonconcentrationProjectionStatement := by
  intro h_osw h_lemma44 h_lemma40 h_norm h_transport
    h_d2s h_frostman h_s2d epsilon hepsilon_pos hepsilon_lt_one
  rcases wz1_finite_osw_one_step_iteration
      h_osw (1 / 4) (epsilon / 16) (by norm_num) (by positivity) with
    ⟨tau, htau, M, hM, hstep⟩
  have hsigma_lt_target : (1 / 4 : ℝ) < 1 - epsilon / 16 := by
    linarith
  rcases exists_first_osw_step htau hsigma_lt_target with
    ⟨N, _hN_pos, hreach, _hovershoot, hstrict⟩
  let lambda : ℝ := epsilon / (100 * M ^ N)
  have hlambda_pos : 0 < lambda := by
    dsimp only [lambda]
    positivity
  have hMN_one : 1 ≤ (M ^ N : ℝ) := by
    have hpow : (1 : ℝ) ^ N ≤ M ^ N := by gcongr
    simpa using hpow
  refine ⟨lambda, hlambda_pos, ?_⟩
  exact wz1_line_nonconcentration_projection_for_zeta
    h_lemma44 h_lemma40 h_norm h_transport h_d2s h_frostman h_s2d
    hepsilon_pos hepsilon_lt_one htau hM hstep hreach hstrict
    rfl hlambda_pos hMN_one

end Kakeya.Assouad
