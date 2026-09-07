import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# Multiplicity bounds from constant multiplicity and mass/volume estimates

Given a shading with constant multiplicity `[m, 2m]`, mass bounds relative to
`F.mass`, and volume bounds, derive `m ≥ δ^(2-σ+ε) * F.enncard` and
`2m ≤ δ^(2-σ-ε) * F.enncard`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Multiply two `realRpowENN` terms. -/
lemma realRpowENN_mul' {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
    Kakeya.realRpowENN delta (a + b) := by
  simp only [Kakeya.realRpowENN]
  have ha : 0 ≤ Real.rpow delta a := Real.rpow_nonneg hdelta.le a
  have h : Real.rpow delta a * Real.rpow delta b = Real.rpow delta (a + b) :=
    (Real.rpow_add hdelta a b).symm
  have h_main : ENNReal.ofReal (Real.rpow delta a) * ENNReal.ofReal (Real.rpow delta b) =
      ENNReal.ofReal (Real.rpow delta (a + b)) := by
    rw [← ENNReal.ofReal_mul ha, h]
  exact h_main

/--
From constant multiplicity `[m, 2m]`, derive mass-volume inequalities:
`m * volume(Y.union) ≤ Y.mass` and `Y.mass ≤ 2 * m * volume(Y.union)`.
-/
lemma constant_multiplicity_mass_volume
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {m : ℕ}
    (hcm : Y.HasConstantMultiplicity m (2 * m)) :
    (m : ENNReal) * MeasureTheory.volume Y.union ≤ Y.mass ∧
    Y.mass ≤ (2 * m : ENNReal) * MeasureTheory.volume Y.union := by
  have h1 : ∀ p ∈ Y.union, (m : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) := by
    intro p hp
    exact_mod_cast (hcm p hp).1
  have h2 : ∀ p ∈ Y.union, (Y.pointMultiplicity p : ENNReal) ≤ (2 * m : ENNReal) := by
    intro p hp
    exact_mod_cast (hcm p hp).2
  have h_zero_outside : ∀ p, p ∉ Y.union → (Y.pointMultiplicity p : ENNReal) = 0 := by
    intro p hp
    let BF := F.toBodyFamily
    have h_i : ∀ (i : Fin BF.card), p ∉ Y.carrier i := by
      intro i h_in
      have h_in_union : p ∈ Y.union := by
        simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq]
        exact ⟨i, h_in⟩
      exact hp h_in_union
    have h_sum : (∑ i : Fin BF.card, (Y.carrier i).indicator (fun _ : Point3 => (1 : ENNReal)) p) = 0 := by
      classical
      apply Finset.sum_eq_zero
      intro i _
      have h_ind : (Y.carrier i).indicator (fun _ : Point3 => (1 : ENNReal)) p = 0 := by
        simp [Set.indicator_apply, h_i i]
      exact h_ind
    have h_eq2 : (Y.pointMultiplicity p : ENNReal) =
        ∑ i : Fin BF.card, (Y.carrier i).indicator (fun _ : Point3 => (1 : ENNReal)) p :=
      coe_pointMultiplicity_eq_sum_indicator Y p
    rw [h_eq2, h_sum]
  have h_eq : (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) = Y.mass :=
    lintegral_pointMultiplicity Y
  have h_indicator : ∀ p : Point3, (Y.pointMultiplicity p : ENNReal) =
      (Y.union).indicator (fun p : Point3 => (Y.pointMultiplicity p : ENNReal)) p := by
    intro p
    by_cases h : p ∈ Y.union
    · simp [h, Set.indicator_apply]
    · have hz : (Y.pointMultiplicity p : ENNReal) = 0 := h_zero_outside p h
      simp [h, hz, Set.indicator_apply]
  have h_set_eq : (∫⁻ p, (Y.pointMultiplicity p : ENNReal)) =
      ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) := by
    rw [lintegral_congr h_indicator]
    rw [lintegral_indicator (measurableSet_shading_union Y)]
  have h3 : (m : ENNReal) * volume Y.union ≤ ∫⁻ p, (Y.pointMultiplicity p : ENNReal) := by
    rw [h_set_eq]
    have h5 : ∫⁻ p in Y.union, (m : ENNReal) ≤ ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) :=
      setLIntegral_mono' (measurableSet_shading_union Y) h1
    have h6 : ∫⁻ p in Y.union, (m : ENNReal) = (m : ENNReal) * volume Y.union := by
      rw [setLIntegral_const]
    rw [h6] at h5
    exact h5
  have h7 : ∫⁻ p, (Y.pointMultiplicity p : ENNReal) ≤ (2 * m : ENNReal) * volume Y.union := by
    rw [h_set_eq]
    have h5 : ∫⁻ p in Y.union, (Y.pointMultiplicity p : ENNReal) ≤ ∫⁻ p in Y.union, (2 * m : ENNReal) :=
      setLIntegral_mono' (measurableSet_shading_union Y) h2
    have h6 : ∫⁻ p in Y.union, (2 * m : ENNReal) = (2 * m : ENNReal) * volume Y.union := by
      rw [setLIntegral_const]
    rw [h6] at h5
    exact h5
  rw [h_eq] at h3 h7
  exact ⟨h3, h7⟩

/--
Derive lower multiplicity bound:
`m ≥ δ^(2-σ+ε) * F.enncard`
from `Y.mass ≥ δ^ε_bal * F.mass`, `F.mass ≥ δ^2 * F.enncard`,
`volume(Y.union) ≤ δ^(σ-ε_bal)`, and `Y.mass ≤ 2m * volume`.
-/
lemma multiplicity_lower_bound
    {delta sigma epsilon epsilon_bal : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {m : ℕ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hcm : Y.HasConstantMultiplicity m (2 * m))
    (hmass_lower : Kakeya.realRpowENN delta epsilon_bal * F.toBodyFamily.mass ≤ Y.mass)
    (hFmass_lower : ENNReal.ofReal (delta ^ 2) * F.enncard ≤ F.toBodyFamily.mass)
    (hvol_upper : volume Y.union ≤ Kakeya.realRpowENN delta (sigma - epsilon_bal))
    (hepsilon_bal_pos : 0 < epsilon_bal)
    (h2eps_lt_eps : 2 * epsilon_bal < epsilon)
    (h_small : Real.rpow delta (2 * epsilon_bal - epsilon) ≥ 2) :
    Kakeya.realRpowENN delta (2 - sigma + epsilon) * F.enncard ≤ (m : ENNReal) := by
  have h_mv := constant_multiplicity_mass_volume hcm
  have h1 : Y.mass ≤ (2 * m : ENNReal) * volume Y.union := h_mv.2
  have h2 : Kakeya.realRpowENN delta epsilon_bal * F.toBodyFamily.mass ≤ (2 * m : ENNReal) * volume Y.union :=
    hmass_lower.trans h1
  have h3 : Kakeya.realRpowENN delta epsilon_bal * (ENNReal.ofReal (delta ^ 2) * F.enncard) ≤
      (2 * m : ENNReal) * volume Y.union := by
    have h4 : Kakeya.realRpowENN delta epsilon_bal * (ENNReal.ofReal (delta ^ 2) * F.enncard) ≤
        Kakeya.realRpowENN delta epsilon_bal * F.toBodyFamily.mass := by
      gcongr
    exact h4.trans h2
  have h_delta2 : ENNReal.ofReal (delta ^ 2) = Kakeya.realRpowENN delta 2 := by
    have h6 : Real.rpow delta (2 : ℝ) = delta ^ 2 := by
      have h7 : Real.rpow delta (↑2 : ℝ) = delta ^ 2 := Real.rpow_natCast delta 2
      simpa using h7
    have h8 : ENNReal.ofReal (delta ^ 2) = ENNReal.ofReal (Real.rpow delta (2 : ℝ)) := by
      rw [h6]
    simpa [Kakeya.realRpowENN] using h8.symm
  have h5 : Kakeya.realRpowENN delta epsilon_bal * ENNReal.ofReal (delta ^ 2) =
      Kakeya.realRpowENN delta (epsilon_bal + 2) := by
    rw [h_delta2, realRpowENN_mul' hdelta]
    <;> ring
  have h3' : (Kakeya.realRpowENN delta epsilon_bal * ENNReal.ofReal (delta ^ 2)) * F.enncard ≤
      (2 * m : ENNReal) * volume Y.union := by
    have h_assoc : Kakeya.realRpowENN delta epsilon_bal * (ENNReal.ofReal (delta ^ 2) * F.enncard) =
        (Kakeya.realRpowENN delta epsilon_bal * ENNReal.ofReal (delta ^ 2)) * F.enncard := by ring
    rw [h_assoc] at h3
    exact h3
  rw [h5] at h3'
  have h6 : Kakeya.realRpowENN delta (epsilon_bal + 2) * F.enncard ≤
      (2 * m : ENNReal) * Kakeya.realRpowENN delta (sigma - epsilon_bal) := by
    calc
      Kakeya.realRpowENN delta (epsilon_bal + 2) * F.enncard
        ≤ (2 * m : ENNReal) * volume Y.union := h3'
      _ ≤ (2 * m : ENNReal) * Kakeya.realRpowENN delta (sigma - epsilon_bal) := by gcongr
  have h7 : (2 * m : ENNReal) * Kakeya.realRpowENN delta (sigma - epsilon_bal) =
      (2 : ENNReal) * ((m : ENNReal) * Kakeya.realRpowENN delta (sigma - epsilon_bal)) := by ring
  rw [h7] at h6
  have h8 : Kakeya.realRpowENN delta (epsilon_bal + 2) * F.enncard ≤
      (2 : ENNReal) * ((m : ENNReal) * Kakeya.realRpowENN delta (sigma - epsilon_bal)) := h6
  have h9 : Kakeya.realRpowENN delta (2 - sigma + epsilon) * F.enncard ≤ (m : ENNReal) := by
    set B := Kakeya.realRpowENN delta (sigma - epsilon_bal) with hB_def
    set A := Kakeya.realRpowENN delta (2 - sigma + epsilon) with hA_def
    set C := Kakeya.realRpowENN delta (2 * epsilon_bal - epsilon) with hC_def
    have h10 : C ≥ (2 : ENNReal) := by
      have h101 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
      rw [h101, hC_def, Kakeya.realRpowENN]
      exact ENNReal.ofReal_mono h_small
    have h11 : Kakeya.realRpowENN delta (epsilon_bal + 2) = A * B * C := by
      simp only [hA_def, hB_def, hC_def, Kakeya.realRpowENN]
      have h12 : Real.rpow delta (2 - sigma + epsilon) *
          Real.rpow delta (sigma - epsilon_bal) *
          Real.rpow delta (2 * epsilon_bal - epsilon) =
          Real.rpow delta (epsilon_bal + 2) := by
        have h13 : (2 - sigma + epsilon) + (sigma - epsilon_bal) + (2 * epsilon_bal - epsilon) = epsilon_bal + 2 := by ring
        have h14 : Real.rpow delta (2 - sigma + epsilon) * Real.rpow delta (sigma - epsilon_bal) =
            Real.rpow delta ((2 - sigma + epsilon) + (sigma - epsilon_bal)) :=
          (Real.rpow_add hdelta _ _).symm
        rw [h14]
        have h15 : Real.rpow delta ((2 - sigma + epsilon) + (sigma - epsilon_bal)) * Real.rpow delta (2 * epsilon_bal - epsilon) =
            Real.rpow delta (((2 - sigma + epsilon) + (sigma - epsilon_bal)) + (2 * epsilon_bal - epsilon)) :=
          (Real.rpow_add hdelta _ _).symm
        rw [h15, h13]
      have h_nonneg1 : 0 ≤ Real.rpow delta (2 - sigma + epsilon) := Real.rpow_nonneg hdelta.le _
      have h_nonneg2 : 0 ≤ Real.rpow delta (sigma - epsilon_bal) := Real.rpow_nonneg hdelta.le _
      rw [← h12]
      rw [ENNReal.ofReal_mul (show 0 ≤ Real.rpow delta (2 - sigma + epsilon) * Real.rpow delta (sigma - epsilon_bal) from mul_nonneg h_nonneg1 h_nonneg2),
          ENNReal.ofReal_mul h_nonneg1]
      <;> ring
    rw [h11] at h8
    have hB_ne_zero : B ≠ 0 := by
      simp [hB_def, Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
    have hB_ne_top : B ≠ ⊤ := by
      simp [hB_def, Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    have h14 : A * B * C * F.enncard ≤ (2 : ENNReal) * ((m : ENNReal) * B) := h8
    have h14' : B * (A * C * F.enncard) ≤ B * (2 * (m : ENNReal)) := by
      have h_left : A * B * C * F.enncard = B * (A * C * F.enncard) := by ring
      have h_right : (2 : ENNReal) * ((m : ENNReal) * B) = B * (2 * (m : ENNReal)) := by ring
      rw [h_left, h_right] at h14
      exact h14
    have h15 : A * C * F.enncard ≤ (2 : ENNReal) * (m : ENNReal) :=
      (ENNReal.mul_le_mul_iff_right hB_ne_zero hB_ne_top).mp h14'
    have h16 : (2 : ENNReal) * (A * F.enncard) ≤ (2 : ENNReal) * (m : ENNReal) := by
      have h_step1 : (2 : ENNReal) * (A * F.enncard) = (A * F.enncard) * (2 : ENNReal) := by ring
      have h_step2 : (A * F.enncard) * (2 : ENNReal) ≤ (A * F.enncard) * C := by
        gcongr
        <;> exact h10
      have h_step3 : (A * F.enncard) * C = A * C * F.enncard := by ring
      calc
        (2 : ENNReal) * (A * F.enncard)
          = (A * F.enncard) * (2 : ENNReal) := h_step1
        _ ≤ (A * F.enncard) * C := h_step2
        _ = A * C * F.enncard := h_step3
        _ ≤ (2 : ENNReal) * (m : ENNReal) := h15
    have h17 : A * F.enncard ≤ (m : ENNReal) := by
      have h18 : (2 : ENNReal) * (A * F.enncard) ≤ (2 : ENNReal) * (m : ENNReal) := h16
      exact (ENNReal.mul_le_mul_iff_right (show (2 : ENNReal) ≠ 0 by norm_num) (show (2 : ENNReal) ≠ ⊤ by norm_num)).mp h18
    simpa [hA_def] using h17
  exact h9

/--
Derive upper multiplicity bound:
`2m ≤ δ^(2-σ-ε) * F.enncard`
from `Y.mass ≤ F.mass`, `F.mass ≤ C * δ^2 * F.enncard`,
`volume(Y.union) ≥ δ^(σ+ε_bal)`, and `m * volume ≤ Y.mass`.
-/
lemma multiplicity_upper_bound
    {delta sigma epsilon epsilon_bal : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {m : ℕ}
    {C : ENNReal}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hcm : Y.HasConstantMultiplicity m (2 * m))
    (hmass_upper : Y.mass ≤ F.toBodyFamily.mass)
    (hFmass_upper : F.toBodyFamily.mass ≤ C * Kakeya.realRpowENN delta 2 * F.enncard)
    (hvol_lower : Kakeya.realRpowENN delta (sigma + epsilon_bal) ≤ volume Y.union)
    (hepsilon_bal_pos : 0 < epsilon_bal)
    (heps_bal_lt_eps : epsilon_bal < epsilon)
    (hC_ne_top : C ≠ ⊤)
    (h_small : C * 2 ≤ Kakeya.realRpowENN delta (epsilon_bal - epsilon)) :
    (2 * m : ENNReal) ≤ Kakeya.realRpowENN delta (2 - sigma - epsilon) * F.enncard := by
  have h_mv := constant_multiplicity_mass_volume hcm
  have h1 : (m : ENNReal) * volume Y.union ≤ Y.mass := h_mv.1
  have h2 : (m : ENNReal) * volume Y.union ≤ F.toBodyFamily.mass := h1.trans hmass_upper
  have h3 : (m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal) ≤ F.toBodyFamily.mass := by
    calc
      (m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal)
        ≤ (m : ENNReal) * volume Y.union := by gcongr
      _ ≤ F.toBodyFamily.mass := h2
  have h4 : (m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal) ≤
      C * Kakeya.realRpowENN delta 2 * F.enncard := h3.trans hFmass_upper
  have h5 : (2 * m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal) ≤
      (C * 2) * Kakeya.realRpowENN delta 2 * F.enncard := by
    calc
      (2 * m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal)
        = 2 * ((m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal)) := by ring
      _ ≤ 2 * (C * Kakeya.realRpowENN delta 2 * F.enncard) := by gcongr
      _ = (C * 2) * Kakeya.realRpowENN delta 2 * F.enncard := by ring
  have h6 : (2 * m : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma - epsilon) * F.enncard := by
    have h7 : Kakeya.realRpowENN delta (sigma + epsilon_bal) * Kakeya.realRpowENN delta (2 - sigma - epsilon) =
        Kakeya.realRpowENN delta (2 + epsilon_bal - epsilon) := by
      rw [realRpowENN_mul' hdelta]
      congr 1
      <;> ring
    have h10 : C * 2 ≤ Kakeya.realRpowENN delta (epsilon_bal - epsilon) := h_small
    have h11 : Kakeya.realRpowENN delta (epsilon_bal - epsilon) * Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN delta (2 + epsilon_bal - epsilon) := by
      rw [realRpowENN_mul' hdelta]
      congr 1
      <;> ring
    have h_step1 : (C * 2) * Kakeya.realRpowENN delta 2 * F.enncard ≤
        Kakeya.realRpowENN delta (epsilon_bal - epsilon) * Kakeya.realRpowENN delta 2 * F.enncard := by
      gcongr
      <;> exact h10
    have h_step2 : Kakeya.realRpowENN delta (epsilon_bal - epsilon) * Kakeya.realRpowENN delta 2 * F.enncard =
        Kakeya.realRpowENN delta (2 + epsilon_bal - epsilon) * F.enncard := by
      have h_assoc : Kakeya.realRpowENN delta (epsilon_bal - epsilon) * Kakeya.realRpowENN delta 2 * F.enncard =
          (Kakeya.realRpowENN delta (epsilon_bal - epsilon) * Kakeya.realRpowENN delta 2) * F.enncard := by ring
      rw [h_assoc, h11]
      <;> ring
    have h_step3 : Kakeya.realRpowENN delta (2 + epsilon_bal - epsilon) * F.enncard =
        Kakeya.realRpowENN delta (sigma + epsilon_bal) *
        (Kakeya.realRpowENN delta (2 - sigma - epsilon) * F.enncard) := by
      have h_eq1 : Kakeya.realRpowENN delta (2 + epsilon_bal - epsilon) =
          Kakeya.realRpowENN delta (sigma + epsilon_bal) * Kakeya.realRpowENN delta (2 - sigma - epsilon) :=
        h7.symm
      rw [h_eq1]
      <;> ring
    have h9 : (C * 2) * Kakeya.realRpowENN delta 2 * F.enncard ≤
        Kakeya.realRpowENN delta (sigma + epsilon_bal) *
        (Kakeya.realRpowENN delta (2 - sigma - epsilon) * F.enncard) := by
      calc
        (C * 2) * Kakeya.realRpowENN delta 2 * F.enncard
          ≤ Kakeya.realRpowENN delta (epsilon_bal - epsilon) * Kakeya.realRpowENN delta 2 * F.enncard := h_step1
        _ = Kakeya.realRpowENN delta (2 + epsilon_bal - epsilon) * F.enncard := h_step2
        _ = Kakeya.realRpowENN delta (sigma + epsilon_bal) *
            (Kakeya.realRpowENN delta (2 - sigma - epsilon) * F.enncard) := h_step3
    have h12_raw : (2 * m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal) ≤
        Kakeya.realRpowENN delta (sigma + epsilon_bal) *
          (Kakeya.realRpowENN delta (2 - sigma - epsilon) * F.enncard) :=
      h5.trans h9
    have h_comm1 : Kakeya.realRpowENN delta (sigma + epsilon_bal) * (2 * m : ENNReal) =
        (2 * m : ENNReal) * Kakeya.realRpowENN delta (sigma + epsilon_bal) := by ring
    have h12 : Kakeya.realRpowENN delta (sigma + epsilon_bal) * (2 * m : ENNReal) ≤
        Kakeya.realRpowENN delta (sigma + epsilon_bal) *
          (Kakeya.realRpowENN delta (2 - sigma - epsilon) * F.enncard) := by
      rw [h_comm1]
      exact h12_raw
    have h13 : Kakeya.realRpowENN delta (sigma + epsilon_bal) ≠ 0 := by
      simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
    have h14 : Kakeya.realRpowENN delta (sigma + epsilon_bal) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact (ENNReal.mul_le_mul_iff_right h13 h14).mp h12
  exact h6

end Kakeya.Assouad
