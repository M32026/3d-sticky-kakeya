module

/-
# Frostman Pole Removal Helper

Given a Frostman probability measure νY on ℝ and a set Θ_bad' with mass
≥ δ^q, construct a radius r > 0 such that removing the open ball
ball(theta2, r) leaves at least half the mass of Θ_bad'.

The radius is r = (δ^q / (2*C_Y))^(1/κ0). Frostman gives
νY(ball(theta2, r)) ≤ C_Y * r^κ0 = δ^q / 2 ≤ νY(Θ_bad') / 2.

Requires the scale condition C_Y * δ^κ0 ≤ δ^q / 2 so that r ≥ δ
(Frostman only controls radii ≥ δ).
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Metric

noncomputable section

/-- Remove a pole neighborhood from a bad-direction set while preserving
at least half the mass.

Given νY Frostman with parameters (δ, κ0, C_Y) and Θ_bad' with mass ≥ δ^q,
there exists r > 0 such that νY(Θ_bad' \ ball(theta2, r)) ≥ (1/2) * νY(Θ_bad').

The scale hypothesis `h_absorb` ensures the chosen radius satisfies r ≥ δ
so that the Frostman ball bound applies. -/
lemma frostman_pole_removal
    {δ κ0 C_Y q : ℝ}
    {νY : Measure ℝ} [IsProbabilityMeasure νY]
    (hν_frost : IsDirectionFrostman δ κ0 C_Y νY)
    {Theta_bad' : Set ℝ}
    (h_mass : νY Theta_bad' ≥ ENNReal.ofReal (δ ^ q))
    (theta2 : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hκ0_pos : 0 < κ0)
    (hC_Y_pos : 0 < C_Y)
    (h_q_pos : 0 < q)
    (h_absorb : C_Y * δ ^ κ0 ≤ δ ^ q / 2) :
    ∃ (r : ℝ), 0 < r ∧ δ ≤ r ∧ r ^ κ0 = δ ^ q / (2 * C_Y) ∧
      νY (Theta_bad' \ ball theta2 r) ≥ (1 / 2 : ENNReal) * νY Theta_bad' := by
  have hν_univ : νY Set.univ = 1 := hν_frost.1
  have hν_supp : νY.support ⊆ Set.Icc 0 1 := hν_frost.2.1
  have hν_reg : ∀ (a r : ℝ), δ ≤ r → r ≤ 1 →
      νY (Set.Icc (a - r) (a + r)) ≤ ENNReal.ofReal (C_Y * r ^ κ0) :=
    hν_frost.2.2

  have hδq_pos : 0 < δ ^ q := Real.rpow_pos_of_pos hδ_pos q
  have h_ratio_pos : 0 < δ ^ q / (2 * C_Y) := by positivity

  set r : ℝ := (δ ^ q / (2 * C_Y)) ^ (1 / κ0) with hr_def

  have hr_pos : 0 < r := Real.rpow_pos_of_pos h_ratio_pos (1 / κ0)

  have h_r_pow : r ^ κ0 = δ ^ q / (2 * C_Y) := by
    rw [hr_def]
    rw [← Real.rpow_mul h_ratio_pos.le]
    have h : (1 / κ0) * κ0 = 1 := by field_simp [hκ0_pos.ne']
    rw [h, Real.rpow_one]

  have h1 : δ ^ κ0 ≤ δ ^ q / (2 * C_Y) := by
    have h11 : C_Y * δ ^ κ0 ≤ δ ^ q / 2 := h_absorb
    have h12 : δ ^ κ0 ≤ (δ ^ q / 2) / C_Y := by
      calc δ ^ κ0
        = (C_Y * δ ^ κ0) / C_Y := by field_simp [hC_Y_pos.ne']
      _ ≤ (δ ^ q / 2) / C_Y := by gcongr
    have h13 : (δ ^ q / 2) / C_Y = δ ^ q / (2 * C_Y) := by ring
    rw [h13] at h12
    exact h12
  have h2 : (δ ^ κ0) ^ (1 / κ0) ≤ (δ ^ q / (2 * C_Y)) ^ (1 / κ0) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : (δ ^ κ0) ^ (1 / κ0) = δ := by
    rw [← Real.rpow_mul hδ_pos.le]
    have h4 : κ0 * (1 / κ0) = 1 := by field_simp [hκ0_pos.ne']
    rw [h4, Real.rpow_one]
  have hδ_le_r : δ ≤ r := by
    calc δ
      = (δ ^ κ0) ^ (1 / κ0) := h3.symm
    _ ≤ (δ ^ q / (2 * C_Y)) ^ (1 / κ0) := h2
    _ = r := hr_def.symm

  have hC_Y_ge1 : 1 ≤ C_Y := by
    have h_supp_null : νY (νY.supportᶜ) = 0 :=
      MeasureTheory.Measure.measure_compl_support (μ := νY)
    have h1 : νY ((Set.Icc (0 : ℝ) 1)ᶜ) = 0 :=
      measure_mono_null (compl_subset_compl.mpr hν_supp) h_supp_null
    have h2 : MeasurableSet (Set.Icc (0 : ℝ) 1) := isClosed_Icc.measurableSet
    have h_disj : Disjoint (Set.Icc (0 : ℝ) 1) ((Set.Icc (0 : ℝ) 1)ᶜ) :=
      disjoint_compl_right
    have h_union : (Set.Icc (0 : ℝ) 1) ∪ ((Set.Icc (0 : ℝ) 1)ᶜ) = Set.univ := by simp
    have h3 : νY Set.univ = νY (Set.Icc (0 : ℝ) 1) + νY ((Set.Icc (0 : ℝ) 1)ᶜ) := by
      rw [← h_union, measure_union h_disj h2.compl]
    have h_Icc_eq_univ : νY (Set.Icc (0 : ℝ) 1) = 1 := by
      rw [h3, h1, add_zero] at hν_univ
      exact hν_univ
    have h4 : νY (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) ≤
        ENNReal.ofReal (C_Y * (1 : ℝ) ^ κ0) :=
      hν_reg (1 / 2 : ℝ) 1 (by linarith) (by norm_num)
    have h5 : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1) := by
      intro x hx
      constructor <;> norm_num <;> linarith [hx.1, hx.2]
    have h9 : νY (Set.Icc ((1 / 2 : ℝ) - 1) ((1 / 2 : ℝ) + 1)) ≥ 1 := by
      calc _ ≥ νY (Set.Icc (0 : ℝ) 1) := measure_mono h5
           _ = 1 := h_Icc_eq_univ
    have h10 : (1 : ENNReal) ≤ ENNReal.ofReal (C_Y * (1 : ℝ) ^ κ0) := le_trans h9 h4
    simpa using h10

  have hr_le_one : r ≤ 1 := by
    have h1 : δ ^ q / (2 * C_Y) < 1 := by
      have hδq_lt_one : δ ^ q < 1 :=
        Real.rpow_lt_one (by linarith) (by linarith) h_q_pos
      have h2 : 2 ≤ 2 * C_Y := by linarith
      calc δ ^ q / (2 * C_Y) ≤ δ ^ q / 2 := by gcongr
           _ < 1 := by linarith [hδq_lt_one]
    have h3 : (δ ^ q / (2 * C_Y)) ^ (1 / κ0) < 1 ^ (1 / κ0) :=
      Real.rpow_lt_rpow h_ratio_pos.le h1 (by positivity)
    simpa [hr_def] using h3.le

  have h_ball_sub_Icc : ball theta2 r ⊆ Set.Icc (theta2 - r) (theta2 + r) := by
    intro x hx
    have h : dist x theta2 < r := hx
    simp only [Real.dist_eq, abs_lt] at h
    exact ⟨by linarith, by linarith⟩

  have h_ball_measure : νY (ball theta2 r) ≤ ENNReal.ofReal (δ ^ q / 2) := by
    calc νY (ball theta2 r)
      ≤ νY (Set.Icc (theta2 - r) (theta2 + r)) := measure_mono h_ball_sub_Icc
    _ ≤ ENNReal.ofReal (C_Y * r ^ κ0) := hν_reg theta2 r hδ_le_r hr_le_one
    _ = ENNReal.ofReal (δ ^ q / 2) := by
      have h_eq : C_Y * r ^ κ0 = δ ^ q / 2 := by
        rw [h_r_pow]
        field_simp [hC_Y_pos.ne']
      rw [h_eq]

  have h_ball_meas : MeasurableSet (ball theta2 r) := isOpen_ball.measurableSet

  set b : ENNReal := νY (Theta_bad' ∩ ball theta2 r) with hb_def
  set c : ENNReal := νY (Theta_bad' \ ball theta2 r) with hc_def
  set a : ENNReal := νY Theta_bad' with ha_def

  have h_partition : a = b + c := by
    simp only [ha_def, hb_def, hc_def]
    rw [← MeasureTheory.measure_inter_add_sdiff Theta_bad' h_ball_meas]

  have h_a_ne_top : a ≠ ⊤ := by
    have h : a ≤ 1 := by
      simp only [ha_def]
      calc νY Theta_bad' ≤ νY Set.univ := measure_mono (Set.subset_univ _)
           _ = 1 := hν_univ
    exact ne_top_of_le_ne_top (by simp) h

  have h_b_le_a : b ≤ a := by
    have h : b ≤ b + c := le_add_right le_rfl
    rw [h_partition] at *; exact h
  have h_b_ne_top : b ≠ ⊤ := ne_top_of_le_ne_top h_a_ne_top h_b_le_a

  have h_inter_le_ball : b ≤ νY (ball theta2 r) := by
    simp only [hb_def]
    have h_sub : Theta_bad' ∩ ball theta2 r ⊆ ball theta2 r := by
      intro x hx
      exact hx.2
    exact measure_mono h_sub

  have h_inter_le : b ≤ ENNReal.ofReal (δ ^ q / 2) :=
    le_trans h_inter_le_ball h_ball_measure

  have h_half_mass : ENNReal.ofReal (δ ^ q / 2) ≤ (1 / 2 : ENNReal) * a := by
    have h1 : ENNReal.ofReal (δ ^ q) ≤ a := by
      simpa [ha_def] using h_mass
    have h2 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ q) ≤ (1 / 2 : ENNReal) * a := by
      gcongr
    have h3 : (1 / 2 : ENNReal) * ENNReal.ofReal (δ ^ q) = ENNReal.ofReal (δ ^ q / 2) := by
      have h_pos1 : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have h_pos2 : 0 ≤ δ ^ q := by positivity
      have h_eq1 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
      rw [h_eq1]
      have h_mul : ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (δ ^ q) =
          ENNReal.ofReal ((1 / 2 : ℝ) * δ ^ q) := by
        simp
      rw [h_mul]
      have h4 : (1 / 2 : ℝ) * δ ^ q = δ ^ q / 2 := by ring
      rw [h4]
    rw [h3] at h2
    exact h2

  have h_b_le_half : b ≤ (1 / 2 : ENNReal) * a :=
    le_trans h_inter_le h_half_mass

  have h_half_add_half : (1 / 2 : ENNReal) * a + (1 / 2 : ENNReal) * a = a := by
    have h3 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
    have h4 : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    have h5 : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) := by
      simp [h3]
    have h2 : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
      rw [h5]
      exact h4
    calc (1 / 2 : ENNReal) * a + (1 / 2 : ENNReal) * a
      = ((1 / 2 : ENNReal) + (1 / 2 : ENNReal)) * a := by rw [add_mul]
    _ = (1 : ENNReal) * a := by rw [h2]
    _ = a := by simp

  have h_main : c ≥ (1 / 2 : ENNReal) * a := by
    set half_a : ENNReal := (1 / 2 : ENNReal) * a with hhalf_def
    have h_eq : b + c = half_a + half_a := by
      have h1 : b + c = a := h_partition.symm
      rw [h1, h_half_add_half]
    have h_c_sub : c = (b + c) - b := by
      exact (ENNReal.add_sub_cancel_left h_b_ne_top).symm
    rw [h_c_sub]
    have h10 : (half_a + half_a) - half_a ≤ (half_a + half_a) - b :=
      tsub_le_tsub_left h_b_le_half (half_a + half_a)
    have h_half_le_a : half_a ≤ a := by
      dsimp only [half_a, hhalf_def]
      calc (1 / 2 : ENNReal) * a
        ≤ (1 : ENNReal) * a := by gcongr; norm_num
      _ = a := by simp
    have h_half_ne_top : half_a ≠ ⊤ := ne_top_of_le_ne_top h_a_ne_top h_half_le_a
    have h11 : (half_a + half_a) - half_a = half_a :=
      ENNReal.add_sub_cancel_left (a := half_a) (b := half_a) h_half_ne_top
    calc (b + c) - b
      = (half_a + half_a) - b := by rw [h_eq]
    _ ≥ (half_a + half_a) - half_a := h10
    _ = half_a := h11

  exact ⟨r, hr_pos, hδ_le_r, h_r_pow, by simpa [ha_def, hc_def] using h_main⟩

end
