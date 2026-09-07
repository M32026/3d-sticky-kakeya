import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSEffectiveLossScheduleStatement

/-!
# Proof of grid_os_effective_loss_schedule

Construct explicit sourceEta, eta schedule, and delta₀ that absorb all
fixed constants in the corrected grid OS iteration.
-/

namespace Kakeya.Assouad

theorem grid_os_effective_loss_schedule :
    GridOSEffectiveLossScheduleStatement := by
  intro epsilon etaMax h_epsilon_pos h_epsilon_lt_one h_etaMax_pos steps
  set c : ℝ := 10 / epsilon ^ 2 with hc_def
  have hc_pos : 0 < c := by positivity
  have hc_gt_one : 1 < c := by
    dsimp only [c]
    have h1 : epsilon ^ 2 < 1 := by nlinarith
    have h2 : 0 < epsilon ^ 2 := by positivity
    have h3 : 10 / epsilon ^ 2 > 10 := by
      have h4 : 0 < epsilon ^ 2 := h2
      have h5 : 10 / epsilon ^ 2 - 10 > 0 := by
        have h6 : 10 / epsilon ^ 2 - 10 = 10 * (1 - epsilon ^ 2) / epsilon ^ 2 := by
          field_simp [h4.ne'] <;> ring
        rw [h6]
        apply div_pos
        · positivity
        · exact h4
      linarith
    linarith
  set sourceEta : ℝ := etaMax / (4 * c ^ steps) with hsourceEta_def
  have hsourceEta_pos : 0 < sourceEta := by positivity
  set eta : ℕ → ℝ := fun index => 4 * sourceEta * c ^ index with heta_def
  set delta₀ : ℝ := Real.rpow (1 / 1600) (1 / sourceEta) with hdelta₀_def

  have hdelta₀_pos : 0 < delta₀ :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hdelta₀_lt_one : delta₀ < 1 := by
    have hbase_pos : (0 : ℝ) ≤ 1 / 1600 := by norm_num
    have hbase_lt_one : (1 / 1600 : ℝ) < 1 := by norm_num
    have hexp_pos : 0 < 1 / sourceEta := by positivity
    exact Real.rpow_lt_one hbase_pos hbase_lt_one hexp_pos
  have hdelta₀_rpow : Real.rpow delta₀ sourceEta = 1 / 1600 := by
    rw [hdelta₀_def]
    have h4 : Real.rpow (Real.rpow (1 / 1600) (1 / sourceEta)) sourceEta =
        Real.rpow (1 / 1600) ((1 / sourceEta) * sourceEta) := by
      exact (Real.rpow_mul (by norm_num) (1 / sourceEta) sourceEta).symm
    rw [h4]
    have h5 : (1 / sourceEta) * sourceEta = 1 := by
      field_simp [hsourceEta_pos.ne'] <;> ring
    rw [h5]
    exact Real.rpow_one (1 / 1600)

  have h_main_bound : ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      ∀ (t : ℝ), t ≥ sourceEta → Real.rpow delta t ≤ 1 / 1600 := by
    intro delta hdelta_pos hdelta_le t ht
    have hdelta_le_one : delta ≤ 1 := by linarith [hdelta₀_lt_one]
    have h1 : Real.rpow delta t ≤ Real.rpow delta sourceEta :=
      Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one ht
    have h2 : Real.rpow delta sourceEta ≤ Real.rpow delta₀ sourceEta :=
      Real.rpow_le_rpow hdelta_pos.le hdelta_le (by linarith)
    rw [hdelta₀_rpow] at h2
    exact le_trans h1 h2

  have heta_ge_source : ∀ index : ℕ, eta index ≥ sourceEta := by
    intro index
    have h1 : c ^ index ≥ 1 := by
      have h11 : 1 ≤ c := by linarith
      have h12 : (1 : ℝ) ^ index ≤ c ^ index := by
        gcongr
        <;> linarith
      simpa using h12
    have h2 : eta index = 4 * sourceEta * c ^ index := by
      simp [heta_def] <;> ring
    rw [h2]
    have h3 : 4 * sourceEta * c ^ index ≥ 4 * sourceEta := by
      have h4 : 0 < 4 * sourceEta := by positivity
      nlinarith
    have h5 : 4 * sourceEta ≥ sourceEta := by linarith [hsourceEta_pos]
    linarith

  have heta_pos : ∀ index : ℕ, index ≤ steps → 0 < eta index := by
    intro index _
    have h2 : eta index = 4 * sourceEta * c ^ index := by
      simp [heta_def] <;> ring
    rw [h2]
    positivity

  have heta_le : ∀ index : ℕ, index ≤ steps → eta index ≤ etaMax := by
    intro index hindex
    have h1 : c ^ index ≤ c ^ steps := by
      gcongr <;> linarith
    have h2 : eta index = 4 * sourceEta * c ^ index := by
      simp [heta_def] <;> ring
    rw [h2, hsourceEta_def]
    have h3 : 4 * (etaMax / (4 * c ^ steps)) * c ^ index ≤ etaMax := by
      have h4 : 4 * (etaMax / (4 * c ^ steps)) * c ^ index =
          etaMax * (c ^ index / c ^ steps) := by
        field_simp [hc_pos.ne'] <;> ring
      rw [h4]
      have h5 : c ^ index / c ^ steps ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact h1
      have h6 : etaMax * (c ^ index / c ^ steps) ≤ etaMax := by
        exact mul_le_of_le_one_right (by linarith) h5
      exact h6
    exact h3

  have heta_formula : ∀ index : ℕ,
      eta index = 4 * sourceEta * Real.rpow c index := by
    intro index
    have h2 : eta index = 4 * sourceEta * c ^ index := by
      simp [heta_def] <;> ring
    have h3 : Real.rpow c index = c ^ index := Real.rpow_natCast c index
    rw [h2, h3] <;> ring

  have h_gridOSNextDensity : ∀ (lambda : ENNReal),
      gridOSNextDensity lambda = ENNReal.ofReal (1 / 1600 : ℝ) * lambda := by
    intro lambda
    simp only [gridOSNextDensity, gridOSRawDensity]
    have h1 : (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2 : ℝ) := by simp
    rw [h1]
    have h21 : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (1 / 800 : ℝ) =
        ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 800 : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
    have h2 : ENNReal.ofReal (1 / 2 : ℝ) * (ENNReal.ofReal (1 / 800 : ℝ) * lambda) =
        ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 800 : ℝ)) * lambda := by
      have h_assoc : ENNReal.ofReal (1 / 2 : ℝ) * (ENNReal.ofReal (1 / 800 : ℝ) * lambda) =
          (ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (1 / 800 : ℝ)) * lambda := by
        rw [mul_assoc]
      rw [h_assoc, h21]
    rw [h2]
    have h3 : (1 / 2 : ℝ) * (1 / 800 : ℝ) = (1 / 1600 : ℝ) := by norm_num
    rw [h3]

  have h_initial_density : ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta (eta 0 / 2) ≤
        terminalCellInitialDensity delta sourceEta := by
    intro delta hdelta_pos hdelta_le
    have h_eta0 : eta 0 = 4 * sourceEta := by
      simp [heta_def] <;> ring
    have h1 : Real.rpow delta (eta 0 / 2) ≤
        (1 / 2 : ℝ) * Real.rpow delta sourceEta := by
      have h_eta0_div2 : eta 0 / 2 = 2 * sourceEta := by
        rw [h_eta0] <;> ring
      rw [h_eta0_div2]
      have h21 : 2 * sourceEta = sourceEta + sourceEta := by ring
      have h2 : Real.rpow delta (2 * sourceEta) =
          Real.rpow delta sourceEta * Real.rpow delta sourceEta := by
        calc
          Real.rpow delta (2 * sourceEta)
            = Real.rpow delta (sourceEta + sourceEta) := by rw [h21]
          _ = Real.rpow delta sourceEta * Real.rpow delta sourceEta :=
            Real.rpow_add hdelta_pos sourceEta sourceEta
      rw [h2]
      have h3 : Real.rpow delta sourceEta ≤ 1 / 2 := by
        have h4 := h_main_bound delta hdelta_pos hdelta_le sourceEta (by linarith)
        linarith
      have h5 : 0 < Real.rpow delta sourceEta := Real.rpow_pos_of_pos hdelta_pos _
      nlinarith
    have h6 : ENNReal.ofReal (Real.rpow delta (eta 0 / 2)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta sourceEta) :=
      ENNReal.ofReal_mono h1
    have h71 : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta sourceEta) =
        ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (Real.rpow delta sourceEta) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    have h72 : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by simp
    have h7 : ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow delta sourceEta) =
        (1 / 2 : ENNReal) * ENNReal.ofReal (Real.rpow delta sourceEta) := by
      rw [h71, h72]
    simpa [Kakeya.realRpowENN, terminalCellInitialDensity, h7] using h6

  have h_initial_parameter : ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      (2 : ENNReal) * Kakeya.realRpowENN delta (-3 * sourceEta) ≤
        Kakeya.realRpowENN delta (-eta 0) := by
    intro delta hdelta_pos hdelta_le
    have h_eta0 : eta 0 = 4 * sourceEta := by
      simp [heta_def] <;> ring
    have h1 : (2 : ℝ) * Real.rpow delta (-3 * sourceEta) ≤
        Real.rpow delta (-eta 0) := by
      have h_eta0' : -eta 0 = -4 * sourceEta := by
        rw [h_eta0] <;> ring
      rw [h_eta0']
      set a : ℝ := Real.rpow delta (3 * sourceEta) with ha_def
      set b : ℝ := Real.rpow delta sourceEta with hb_def
      have ha_pos : 0 < a := Real.rpow_pos_of_pos hdelta_pos _
      have hb_pos : 0 < b := Real.rpow_pos_of_pos hdelta_pos _
      have h_eq4 : Real.rpow delta (4 * sourceEta) = b * a := by
        have h_sum : 4 * sourceEta = sourceEta + 3 * sourceEta := by ring
        have h_rpow : Real.rpow delta (sourceEta + 3 * sourceEta) =
            Real.rpow delta sourceEta * Real.rpow delta (3 * sourceEta) :=
          Real.rpow_add hdelta_pos sourceEta (3 * sourceEta)
        calc
          Real.rpow delta (4 * sourceEta)
            = Real.rpow delta (sourceEta + 3 * sourceEta) := by rw [h_sum]
          _ = Real.rpow delta sourceEta * Real.rpow delta (3 * sourceEta) := h_rpow
          _ = b * a := by simp [hb_def, ha_def]
      have h4 : b ≤ 1 / 2 := by
        simp only [hb_def]
        have h5 := h_main_bound delta hdelta_pos hdelta_le sourceEta (by linarith)
        linarith
      have h_neg3 : Real.rpow delta (-3 * sourceEta) = a⁻¹ := by
        have h : -3 * sourceEta = -(3 * sourceEta) := by ring
        have h_rpow : Real.rpow delta (-(3 * sourceEta)) = (Real.rpow delta (3 * sourceEta))⁻¹ :=
          Real.rpow_neg hdelta_pos.le (3 * sourceEta)
        calc
          Real.rpow delta (-3 * sourceEta)
            = Real.rpow delta (-(3 * sourceEta)) := by rw [h]
          _ = (Real.rpow delta (3 * sourceEta))⁻¹ := h_rpow
          _ = a⁻¹ := by simp [ha_def]
      have h_neg4 : Real.rpow delta (-4 * sourceEta) = (b * a)⁻¹ := by
        have h : -4 * sourceEta = -(4 * sourceEta) := by ring
        have h_rpow : Real.rpow delta (-(4 * sourceEta)) = (Real.rpow delta (4 * sourceEta))⁻¹ :=
          Real.rpow_neg hdelta_pos.le (4 * sourceEta)
        calc
          Real.rpow delta (-4 * sourceEta)
            = Real.rpow delta (-(4 * sourceEta)) := by rw [h]
          _ = (Real.rpow delta (4 * sourceEta))⁻¹ := h_rpow
          _ = (b * a)⁻¹ := by rw [h_eq4]
      rw [h_neg3, h_neg4]
      have h5 : (2 : ℝ) * a⁻¹ ≤ (b * a)⁻¹ := by
        have h6 : (b * a)⁻¹ = b⁻¹ * a⁻¹ := by
          field_simp [ha_pos.ne', hb_pos.ne'] <;> ring
        rw [h6]
        have h7 : 2 ≤ b⁻¹ := by
          have h8 : b ≤ 1 / 2 := h4
          have h9 : 0 < b := hb_pos
          calc
            2 = (1 / 2 : ℝ)⁻¹ := by norm_num
            _ ≤ b⁻¹ := by gcongr
        have h10 : 0 < a⁻¹ := by positivity
        nlinarith
      exact h5
    have h6 : (0 : ℝ) ≤ (2 : ℝ) * Real.rpow delta (-3 * sourceEta) := by
      have h_pos : 0 < Real.rpow delta (-3 * sourceEta) := Real.rpow_pos_of_pos hdelta_pos _
      exact mul_nonneg (by norm_num) h_pos.le
    have h7 : ENNReal.ofReal ((2 : ℝ) * Real.rpow delta (-3 * sourceEta)) ≤
        ENNReal.ofReal (Real.rpow delta (-eta 0)) :=
      ENNReal.ofReal_mono h1
    have h8 : ENNReal.ofReal ((2 : ℝ) * Real.rpow delta (-3 * sourceEta)) =
        (2 : ENNReal) * ENNReal.ofReal (Real.rpow delta (-3 * sourceEta)) := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> norm_num
    simpa [Kakeya.realRpowENN, h8] using h7

  have h_transition_density : ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      ∀ (index : ℕ), index < steps → ∀ (scale rho : ℝ),
        delta ≤ scale → scale ≤ 1 → 0 < rho →
        rho < Real.rpow delta (epsilon ^ 2) →
          Kakeya.realRpowENN rho (eta (index + 1) / 2) ≤
            gridOSNextDensity (Kakeya.realRpowENN scale (4 * eta index)) := by
    intro delta hdelta_pos hdelta_le index hindex scale rho
      hdelta_le_scale hscale_le_one hrho_pos hrho_lt
    have h_eta_next : eta (index + 1) = c * eta index := by
      simp [heta_def, hc_def] <;> ring
    have h_exponent_eq : epsilon ^ 2 * (eta (index + 1) / 2) = 5 * eta index := by
      rw [h_eta_next, hc_def]
      field_simp [h_epsilon_pos.ne'] <;> ring
    have h_eta_index_pos : 0 < eta index := heta_pos index (Nat.le_of_lt hindex)
    have h1 : Real.rpow rho (eta (index + 1) / 2) <
        Real.rpow delta (5 * eta index) := by
      have h_exp_pos : 0 < eta (index + 1) / 2 := by
        have h_le : index + 1 ≤ steps := Nat.succ_le_of_lt hindex
        have h_pos : 0 < eta (index + 1) := heta_pos (index + 1) h_le
        linarith
      have h_strict : Real.rpow rho (eta (index + 1) / 2) <
          Real.rpow (Real.rpow delta (epsilon ^ 2)) (eta (index + 1) / 2) := by
        exact Real.rpow_lt_rpow hrho_pos.le hrho_lt h_exp_pos
      have h2 : Real.rpow (Real.rpow delta (epsilon ^ 2)) (eta (index + 1) / 2) =
          Real.rpow delta (epsilon ^ 2 * (eta (index + 1) / 2)) :=
        (Real.rpow_mul hdelta_pos.le (epsilon ^ 2) (eta (index + 1) / 2)).symm
      rw [h2, h_exponent_eq] at h_strict
      exact h_strict
    have h3 : Real.rpow delta (5 * eta index) ≤
        (1 / 1600 : ℝ) * Real.rpow scale (4 * eta index) := by
      have h4 : Real.rpow scale (4 * eta index) ≥ Real.rpow delta (4 * eta index) :=
        Real.rpow_le_rpow hdelta_pos.le hdelta_le_scale (by positivity)
      have h51 : 5 * eta index = eta index + 4 * eta index := by ring
      have h5 : Real.rpow delta (5 * eta index) =
          Real.rpow delta (eta index) * Real.rpow delta (4 * eta index) := by
        calc
          Real.rpow delta (5 * eta index)
            = Real.rpow delta (eta index + 4 * eta index) := by rw [h51]
          _ = Real.rpow delta (eta index) * Real.rpow delta (4 * eta index) :=
            Real.rpow_add hdelta_pos (eta index) (4 * eta index)
      rw [h5]
      have h6 : Real.rpow delta (eta index) ≤ 1 / 1600 :=
        h_main_bound delta hdelta_pos hdelta_le (eta index) (heta_ge_source index)
      have h7 : 0 < Real.rpow delta (4 * eta index) :=
        Real.rpow_pos_of_pos hdelta_pos _
      nlinarith
    have h8 : Real.rpow rho (eta (index + 1) / 2) ≤
        (1 / 1600 : ℝ) * Real.rpow scale (4 * eta index) :=
      le_trans h1.le h3
    have h9 : ENNReal.ofReal (Real.rpow rho (eta (index + 1) / 2)) ≤
        ENNReal.ofReal ((1 / 1600 : ℝ) * Real.rpow scale (4 * eta index)) :=
      ENNReal.ofReal_mono h8
    have h10 : ENNReal.ofReal ((1 / 1600 : ℝ) * Real.rpow scale (4 * eta index)) =
        ENNReal.ofReal (1 / 1600 : ℝ) * ENNReal.ofReal (Real.rpow scale (4 * eta index)) := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> norm_num
    rw [h_gridOSNextDensity]
    simpa [Kakeya.realRpowENN, h10] using h9

  have h_transition_parameter : ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
      ∀ (index : ℕ), index < steps → ∀ (scale rho : ℝ),
        delta ≤ scale → scale ≤ 1 → 0 < rho →
        rho < Real.rpow delta (epsilon ^ 2) →
          (8 : ENNReal) * Kakeya.realRpowENN scale (-eta index) ≤
            Kakeya.realRpowENN rho (-eta (index + 1)) := by
    intro delta hdelta_pos hdelta_le index hindex scale rho
      hdelta_le_scale hscale_le_one hrho_pos hrho_lt
    have h_eta_next : eta (index + 1) = c * eta index := by
      simp [heta_def, hc_def] <;> ring
    have h_exponent_eq : epsilon ^ 2 * eta (index + 1) = 10 * eta index := by
      rw [h_eta_next, hc_def]
      field_simp [h_epsilon_pos.ne'] <;> ring
    have h_eta_index_pos : 0 < eta index := heta_pos index (Nat.le_of_lt hindex)
    have h1 : Real.rpow rho (-eta (index + 1)) >
        Real.rpow delta (-10 * eta index) := by
      have h_exp_neg : -eta (index + 1) < 0 := by
        have h_le : index + 1 ≤ steps := Nat.succ_le_of_lt hindex
        have h_pos : 0 < eta (index + 1) := heta_pos (index + 1) h_le
        linarith
      have h_strict : Real.rpow rho (-eta (index + 1)) >
          Real.rpow (Real.rpow delta (epsilon ^ 2)) (-eta (index + 1)) := by
        set y : ℝ := eta (index + 1) with hy_def
        have hy_pos : 0 < y := heta_pos (index + 1) (Nat.succ_le_of_lt hindex)
        have h_base_pos : 0 < Real.rpow delta (epsilon ^ 2) := Real.rpow_pos_of_pos hdelta_pos _
        have h1 : Real.rpow rho y < Real.rpow (Real.rpow delta (epsilon ^ 2)) y :=
          Real.rpow_lt_rpow hrho_pos.le hrho_lt hy_pos
        have h_rho_neg : Real.rpow rho (-y) = (Real.rpow rho y)⁻¹ :=
          Real.rpow_neg hrho_pos.le y
        have h_base_neg : Real.rpow (Real.rpow delta (epsilon ^ 2)) (-y) =
            (Real.rpow (Real.rpow delta (epsilon ^ 2)) y)⁻¹ :=
          Real.rpow_neg h_base_pos.le y
        rw [h_rho_neg, h_base_neg]
        have h_pos1 : 0 < Real.rpow rho y := Real.rpow_pos_of_pos hrho_pos y
        have h_pos2 : 0 < Real.rpow (Real.rpow delta (epsilon ^ 2)) y :=
          Real.rpow_pos_of_pos h_base_pos y
        have h4 : (Real.rpow rho y)⁻¹ > (Real.rpow (Real.rpow delta (epsilon ^ 2)) y)⁻¹ := by
          have h5 : (Real.rpow rho y)⁻¹ - (Real.rpow (Real.rpow delta (epsilon ^ 2)) y)⁻¹ =
              ((Real.rpow (Real.rpow delta (epsilon ^ 2)) y) - Real.rpow rho y) /
              ((Real.rpow rho y) * (Real.rpow (Real.rpow delta (epsilon ^ 2)) y)) := by
            field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
          have h6 : 0 < ((Real.rpow (Real.rpow delta (epsilon ^ 2)) y) - Real.rpow rho y) /
              ((Real.rpow rho y) * (Real.rpow (Real.rpow delta (epsilon ^ 2)) y)) := by
            apply div_pos
            · linarith
            · exact mul_pos h_pos1 h_pos2
          have h7 : 0 < (Real.rpow rho y)⁻¹ - (Real.rpow (Real.rpow delta (epsilon ^ 2)) y)⁻¹ := by
            rw [h5]
            exact h6
          linarith
        exact h4
      have h21 : epsilon ^ 2 * (-eta (index + 1)) = -(epsilon ^ 2 * eta (index + 1)) := by ring
      have h2 : Real.rpow (Real.rpow delta (epsilon ^ 2)) (-eta (index + 1)) =
          Real.rpow delta (-(epsilon ^ 2 * eta (index + 1))) := by
        have h_mul : Real.rpow delta (epsilon ^ 2 * (-eta (index + 1))) =
            Real.rpow (Real.rpow delta (epsilon ^ 2)) (-eta (index + 1)) :=
          Real.rpow_mul hdelta_pos.le (epsilon ^ 2) (-eta (index + 1))
        have h22 : Real.rpow delta (epsilon ^ 2 * (-eta (index + 1))) =
            Real.rpow delta (-(epsilon ^ 2 * eta (index + 1))) := by rw [h21]
        exact h_mul.symm.trans h22
      calc
        Real.rpow rho (-eta (index + 1))
          > Real.rpow (Real.rpow delta (epsilon ^ 2)) (-eta (index + 1)) := h_strict
        _ = Real.rpow delta (-(epsilon ^ 2 * eta (index + 1))) := h2
        _ = Real.rpow delta (-10 * eta index) := by
          have h3 : -(epsilon ^ 2 * eta (index + 1)) = -10 * eta index := by
            rw [h_exponent_eq] <;> ring
          rw [h3]
    set a : ℝ := Real.rpow delta (eta index) with ha_def
    set b : ℝ := Real.rpow delta (9 * eta index) with hb_def
    have ha_pos : 0 < a := Real.rpow_pos_of_pos hdelta_pos _
    have hb_pos : 0 < b := Real.rpow_pos_of_pos hdelta_pos _
    have h_b_le : b ≤ 1 / 8 := by
      simp only [hb_def]
      have h8 : 9 * eta index ≥ sourceEta := by
        have h9 : eta index ≥ sourceEta := heta_ge_source index
        nlinarith [h_eta_index_pos]
      have h10 := h_main_bound delta hdelta_pos hdelta_le (9 * eta index) h8
      linarith
    have h_neg_eta : Real.rpow delta (-eta index) = a⁻¹ := by
      have h : -eta index = -(eta index) := by ring
      have h_rpow : Real.rpow delta (-(eta index)) = (Real.rpow delta (eta index))⁻¹ :=
        Real.rpow_neg hdelta_pos.le (eta index)
      calc
        Real.rpow delta (-eta index)
          = Real.rpow delta (-(eta index)) := by rw [h]
        _ = (Real.rpow delta (eta index))⁻¹ := h_rpow
        _ = a⁻¹ := by simp [ha_def]
    have h_neg10 : Real.rpow delta (-10 * eta index) = (a * b)⁻¹ := by
      have h_sum : 10 * eta index = eta index + 9 * eta index := by ring
      have h_eq10 : Real.rpow delta (10 * eta index) = a * b := by
        simp only [ha_def, hb_def]
        have h_rpow : Real.rpow delta (eta index + 9 * eta index) =
            Real.rpow delta (eta index) * Real.rpow delta (9 * eta index) :=
          Real.rpow_add hdelta_pos (eta index) (9 * eta index)
        calc
          Real.rpow delta (10 * eta index)
            = Real.rpow delta (eta index + 9 * eta index) := by rw [h_sum]
          _ = Real.rpow delta (eta index) * Real.rpow delta (9 * eta index) := h_rpow
          _ = a * b := by simp [ha_def, hb_def]
      have h : -10 * eta index = -(10 * eta index) := by ring
      have h_rpow_neg : Real.rpow delta (-(10 * eta index)) = (Real.rpow delta (10 * eta index))⁻¹ :=
        Real.rpow_neg hdelta_pos.le (10 * eta index)
      calc
        Real.rpow delta (-10 * eta index)
          = Real.rpow delta (-(10 * eta index)) := by rw [h]
        _ = (Real.rpow delta (10 * eta index))⁻¹ := h_rpow_neg
        _ = (a * b)⁻¹ := by rw [h_eq10]
    have h3 : (8 : ℝ) * Real.rpow scale (-eta index) ≤
        Real.rpow delta (-10 * eta index) := by
      calc
        (8 : ℝ) * Real.rpow scale (-eta index)
          ≤ (8 : ℝ) * Real.rpow delta (-eta index) := by
            gcongr
            exact Real.rpow_le_rpow_of_nonpos hdelta_pos hdelta_le_scale (by linarith)
        _ = (8 : ℝ) * a⁻¹ := by
          rw [h_neg_eta] <;> ring
        _ ≤ (a * b)⁻¹ := by
          have h6 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
            field_simp [ha_pos.ne', hb_pos.ne'] <;> ring
          rw [h6]
          have h7 : 8 ≤ b⁻¹ := by
            have h8 : b ≤ 1 / 8 := h_b_le
            have h9 : 0 < b := hb_pos
            calc
              8 = (1 / 8 : ℝ)⁻¹ := by norm_num
              _ ≤ b⁻¹ := by gcongr
          have h10 : 0 < a⁻¹ := by positivity
          nlinarith
        _ = Real.rpow delta (-10 * eta index) := h_neg10.symm
    have h4 : (8 : ℝ) * Real.rpow scale (-eta index) ≤
        Real.rpow rho (-eta (index + 1)) :=
      le_trans h3 h1.le
    have h5 : (0 : ℝ) ≤ (8 : ℝ) * Real.rpow scale (-eta index) := by
      have h_scale_pos : 0 < scale := lt_of_lt_of_le hdelta_pos hdelta_le_scale
      have h_pos : 0 < Real.rpow scale (-eta index) := Real.rpow_pos_of_pos h_scale_pos _
      exact mul_nonneg (by norm_num) h_pos.le
    have h6 : ENNReal.ofReal ((8 : ℝ) * Real.rpow scale (-eta index)) ≤
        ENNReal.ofReal (Real.rpow rho (-eta (index + 1))) :=
      ENNReal.ofReal_mono h4
    have h7 : ENNReal.ofReal ((8 : ℝ) * Real.rpow scale (-eta index)) =
        (8 : ENNReal) * ENNReal.ofReal (Real.rpow scale (-eta index)) := by
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 by norm_num)]
      <;> norm_num
    simpa [Kakeya.realRpowENN, h7] using h6

  refine' ⟨sourceEta, eta, hsourceEta_pos, heta_formula, heta_pos, heta_le,
    delta₀, hdelta₀_pos, hdelta₀_lt_one, h_initial_density, h_initial_parameter,
    h_transition_density, h_transition_parameter⟩

end Kakeya.Assouad
