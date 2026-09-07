import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper
import MyLeanRepo.Kakeya.Assouad.Hairbrush.ExpandedAssemblyAlgebra
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HardPowerHelpers
import MyLeanRepo.Kakeya.Assouad.Hairbrush.RealCoreAlgebra

/-!
# Homogeneous hard-branch power assembly

This target contains only the ENNReal/rpow algebra combining the numerical
content of (B.15), (B.18)--(B.20), (B.24), and (B.27) into (B.28).
-/

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_hard_power :
    HairbrushHomogeneousHardPowerStatement := by
  intro zeta stemLoss bandLoss familyLoss hairLoss cordobaLoss outputExponent
    hzeta_pos hzeta_lt_one hstem hband hfamily hhair hcordoba hgap
  set p : ℝ := hairbrushHomogeneousDensityPower zeta with hp_def
  set total : ℝ := 1 + stemLoss + bandLoss + familyLoss + hairLoss + cordobaLoss with htotal_def
  set gap : ℝ := outputExponent - total with hgap_def
  have hp_pos : 0 < p := by
    rw [hp_def, hairbrushHomogeneousDensityPower]
    have h1 : 0 < 1 + 3 * zeta := by linarith
    have h2 : 0 < 1 - zeta := by linarith
    exact div_pos h1 h2
  have hgap_pos : 0 < gap := by
    rw [hgap_def] <;> linarith
  set c : ℝ := 4 * Real.rpow 200 p with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    have h1 : 0 < Real.rpow 200 p := Real.rpow_pos_of_pos (by norm_num) p
    positivity
  rcases Subunit.exists_delta₀_mul_pow_le_one c hc_pos gap hgap_pos with
    ⟨d0, hd0_pos, hd0_le_one, h_ineq⟩
  set delta₀ : ℝ := min d0 (1 / 1000) with hdelta₀_def
  have hdelta₀_pos : 0 < delta₀ := by
    rw [hdelta₀_def]
    exact lt_min hd0_pos (by norm_num)
  have hdelta₀_le_thousandth : delta₀ ≤ 1 / 1000 := by
    rw [hdelta₀_def] <;> exact min_le_right _ _
  refine' ⟨delta₀, hdelta₀_pos, hdelta₀_le_thousandth, _⟩
  intro δ hδ hδ_le_delta₀ theta radius htheta_pos htheta_le_one
    hδ_le_radius hradius_le_two
  intro ambientCount hairCount refinedCount brushCount bandCount mu
    layerDensity hairDensity refinedDensity targetVolume
    h_ac0 h_acTop h_hc0 h_hcTop h_rc0 h_rcTop h_bc0 h_bcTop
    h_bdc0 h_bdcTop h_mu0 h_muTop h_ld0 h_ldTop h_hd0 h_hdTop
    h_rd0 h_rdTop h_tvTop
  intro h_layer h_hair_ret h_family h_ref_den h_radius_den h_stem h_band h_cordoba
  have hδ_lt_one : δ < 1 := by
    have h : delta₀ ≤ 1 / 1000 := hdelta₀_le_thousandth
    linarith
  have hradius_pos : 0 < radius := lt_of_lt_of_le hδ hδ_le_radius
  have hd0' : δ ≤ d0 := by
    have h : delta₀ ≤ d0 := by
      rw [hdelta₀_def] <;> exact min_le_left _ _
    exact le_trans hδ_le_delta₀ h
  have h_absorb : c * Real.rpow δ gap ≤ 1 := h_ineq δ hδ hd0'
  -- Real projections of ENNReal quantities
  set ac : ℝ := ambientCount.toReal with hac_def
  set hc : ℝ := hairCount.toReal with hhc_def
  set rc : ℝ := refinedCount.toReal with hrc_def
  set bc : ℝ := brushCount.toReal with hbc_def
  set bdc : ℝ := bandCount.toReal with hbdc_def
  set m : ℝ := mu.toReal with hm_def
  set ld : ℝ := layerDensity.toReal with hld_def
  set hd : ℝ := hairDensity.toReal with hhd_def
  set rd : ℝ := refinedDensity.toReal with hrd_def
  set tv : ℝ := targetVolume.toReal with htv_def
  have h_pos1 : 0 < ac := ENNReal.toReal_pos h_ac0 h_acTop
  have h_pos2 : 0 < hc := ENNReal.toReal_pos h_hc0 h_hcTop
  have h_pos3 : 0 < rc := ENNReal.toReal_pos h_rc0 h_rcTop
  have h_pos4 : 0 < bc := ENNReal.toReal_pos h_bc0 h_bcTop
  have h_pos5 : 0 < bdc := ENNReal.toReal_pos h_bdc0 h_bdcTop
  have h_pos6 : 0 < m := ENNReal.toReal_pos h_mu0 h_muTop
  have h_pos7 : 0 < ld := ENNReal.toReal_pos h_ld0 h_ldTop
  have h_pos8 : 0 < hd := ENNReal.toReal_pos h_hd0 h_hdTop
  have h_pos9 : 0 < rd := ENNReal.toReal_pos h_rd0 h_rdTop
  have h_pos10 : 0 ≤ tv := ENNReal.toReal_nonneg
  -- Convert hypothesis: layerDensity / 2 ≤ hairDensity
  have h_ld_div2_top : (layerDensity / 2) ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · exact h_ldTop
    · simp
  have h_layer' : ld / 2 ≤ hd := by
    have h1 : (layerDensity / 2).toReal ≤ hairDensity.toReal :=
      toReal_le_of_ennreal_le h_ld_div2_top h_hdTop h_layer
    have h2 : (layerDensity / 2).toReal = ld / 2 := by
      rw [toReal_div h_ld0 h_ldTop (by simp) (by simp)]
      <;> simp [hld_def]
      <;> norm_num
    rw [h2] at h1
    exact h1
  -- Convert hypothesis: hair retention
  have h_rpowH_top : (Kakeya.realRpowENN δ hairLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have h_hairLHS_top : (Kakeya.realRpowENN δ hairLoss * layerDensity * ambientCount) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top h_rpowH_top h_ldTop) h_acTop
  have h_hairRHS_top : (hairDensity * hairCount) ≠ ⊤ := ENNReal.mul_ne_top h_hdTop h_hcTop
  have h_hair_ret' : Real.rpow δ hairLoss * ld * ac ≤ hd * hc := by
    have hLHS : (Kakeya.realRpowENN δ hairLoss * layerDensity * ambientCount).toReal =
        Real.rpow δ hairLoss * ld * ac := by
      simp [toReal_mul, toReal_realRpowENN hδ, hac_def, hld_def]
      <;> ring
    have hRHS : (hairDensity * hairCount).toReal = hd * hc := by
      simp [toReal_mul, hhd_def, hhc_def]
    have h : (Kakeya.realRpowENN δ hairLoss * layerDensity * ambientCount).toReal ≤
        (hairDensity * hairCount).toReal :=
      toReal_le_of_ennreal_le h_hairLHS_top h_hairRHS_top h_hair_ret
    rw [hLHS, hRHS] at h
    exact h
  -- Convert hypothesis: family retention
  have h_rpowF_top : (Kakeya.realRpowENN δ familyLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have h_familyLHS_top : (Kakeya.realRpowENN δ familyLoss * hairCount) ≠ ⊤ :=
    ENNReal.mul_ne_top h_rpowF_top h_hcTop
  have h_family' : Real.rpow δ familyLoss * hc ≤ rc := by
    have hLHS : (Kakeya.realRpowENN δ familyLoss * hairCount).toReal =
        Real.rpow δ familyLoss * hc := by
      simp [toReal_mul, toReal_realRpowENN hδ, hhc_def]
    have hRHS : refinedCount.toReal = rc := by simp [hrc_def]
    have h := toReal_le_of_ennreal_le h_familyLHS_top h_rcTop h_family
    rw [hLHS, hRHS] at h
    exact h
  -- Convert hypothesis: refined density
  have h_ofReal_rpow_top : (ENNReal.ofReal (Real.rpow radius zeta)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_refLHS_top : (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity) ≠ ⊤ :=
    ENNReal.mul_ne_top h_ofReal_rpow_top h_hdTop
  have h_ref_den' : Real.rpow radius zeta * hd ≤ rd := by
    have h1 : 0 ≤ Real.rpow radius zeta := Real.rpow_nonneg hradius_pos.le zeta
    have hLHS : (ENNReal.ofReal (Real.rpow radius zeta) * hairDensity).toReal =
        Real.rpow radius zeta * hd := by
      rw [toReal_mul h_ofReal_rpow_top h_hdTop, toReal_ofReal h1, hhd_def]
      <;> ring
    have hRHS : refinedDensity.toReal = rd := by simp [hrd_def]
    have h := toReal_le_of_ennreal_le h_refLHS_top h_rdTop h_ref_den
    rw [hLHS, hRHS] at h
    exact h
  -- Convert hypothesis: radius-density relation
  have h_radius_den' : hd ≤ 100 * Real.rpow radius (1 - zeta) := by
    have hRHS : (ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow radius (1 - zeta))).toReal =
        100 * Real.rpow radius (1 - zeta) := by
      have h1 : 0 ≤ Real.rpow radius (1 - zeta) := Real.rpow_nonneg hradius_pos.le (1 - zeta)
      rw [toReal_mul ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
      rw [toReal_ofReal (show (0 : ℝ) ≤ 100 by norm_num), toReal_ofReal h1]
      <;> ring
    have h_radiusRHS_top : (ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow radius (1 - zeta))) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have h := toReal_le_of_ennreal_le h_hdTop h_radiusRHS_top h_radius_den
    rw [hRHS] at h
    exact h
  -- Convert hypothesis: stem averaging
  have h_stem' : Real.rpow δ stemLoss * theta * m * rd * rc / (δ * ac) ≤ bc := by
    let denom : ENNReal := ENNReal.ofReal δ * ambientCount
    have hdenom0 : denom ≠ 0 := by
      have h1 : ENNReal.ofReal δ ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff] <;> linarith
      have h2 : denom = ENNReal.ofReal δ * ambientCount := by simp [denom]
      rw [h2]
      exact mul_ne_zero h1 h_ac0
    have hdenomTop : denom ≠ ⊤ := by
      have h : denom = ENNReal.ofReal δ * ambientCount := by simp [denom]
      rw [h]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_acTop
    have hLHS : (Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * mu *
          refinedDensity * refinedCount / denom).toReal =
        Real.rpow δ stemLoss * theta * m * rd * rc / (δ * ac) := by
      have htheta_nonneg : 0 ≤ theta := by linarith
      have hδ_nonneg : 0 ≤ δ := by linarith
      have hdenom_real : denom.toReal = δ * ac := by
        simp [denom, toReal_mul, toReal_ofReal hδ_nonneg, hac_def]
        <;> ring
      simp [toReal_div hdenom0 hdenomTop, toReal_mul, toReal_realRpowENN hδ, toReal_ofReal,
            htheta_nonneg, hδ_nonneg, hrd_def, hrc_def, hm_def, hac_def, hdenom_real]
      <;> field_simp [hδ.ne', h_pos1.ne'] <;> ring
    have hRHS : brushCount.toReal = bc := by simp [hbc_def]
    have h_rpowS_top : (Kakeya.realRpowENN δ stemLoss) ≠ ⊤ := by simp [Kakeya.realRpowENN]
    have h_ofRealTheta_top : (ENNReal.ofReal theta) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_stem_num_top : (Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * mu * refinedDensity * refinedCount) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h_rpowS_top h_ofRealTheta_top) h_muTop) h_rdTop) h_rcTop
    have h_stemLHS_top : (Kakeya.realRpowENN δ stemLoss * ENNReal.ofReal theta * mu * refinedDensity * refinedCount / denom) ≠ ⊤ := by
      exact ENNReal.div_ne_top h_stem_num_top hdenom0
    have h := toReal_le_of_ennreal_le h_stemLHS_top h_bcTop h_stem
    rw [hLHS, hRHS] at h
    exact h
  -- Convert hypothesis: band retention
  have h_rpowB_top : (Kakeya.realRpowENN δ bandLoss) ≠ ⊤ := by simp [Kakeya.realRpowENN]
  have h_bandLHS_top : (Kakeya.realRpowENN δ bandLoss * brushCount) ≠ ⊤ :=
    ENNReal.mul_ne_top h_rpowB_top h_bcTop
  have h_band' : Real.rpow δ bandLoss * bc ≤ bdc := by
    have hLHS : (Kakeya.realRpowENN δ bandLoss * brushCount).toReal =
        Real.rpow δ bandLoss * bc := by
      simp [toReal_mul, toReal_realRpowENN hδ, hbc_def]
    have hRHS : bandCount.toReal = bdc := by simp [hbdc_def]
    have h := toReal_le_of_ennreal_le h_bandLHS_top h_bdcTop h_band
    rw [hLHS, hRHS] at h
    exact h
  -- Convert hypothesis: Córdoba
  have h_cordoba' : Real.rpow δ cordobaLoss * radius * rd^2 * bdc * δ^2 ≤ tv := by
    have hLHS : (Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius *
          refinedDensity ^ 2 * bandCount * ENNReal.ofReal (δ ^ 2)).toReal =
        Real.rpow δ cordobaLoss * radius * rd^2 * bdc * δ^2 := by
      have hradius_nonneg : 0 ≤ radius := by linarith
      have hδ2_nonneg : 0 ≤ δ ^ 2 := by positivity
      have h_rd2 : (refinedDensity ^ 2).toReal = rd^2 := by
        rw [ENNReal.toReal_pow] <;> simp [hrd_def]
      simp [toReal_mul, toReal_realRpowENN hδ, toReal_ofReal, hradius_nonneg,
            hδ2_nonneg, h_rd2, hbdc_def]
      <;> ring
    have hRHS : targetVolume.toReal = tv := by simp [htv_def]
    have h_rpowC_top : (Kakeya.realRpowENN δ cordobaLoss) ≠ ⊤ := by simp [Kakeya.realRpowENN]
    have h_ofRealRadius_top : (ENNReal.ofReal radius) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_ofRealD2_top : (ENNReal.ofReal (δ ^ 2)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_rd2_top : (refinedDensity ^ 2) ≠ ⊤ := by
      exact ENNReal.pow_ne_top h_rdTop
    have h_cordobaLHS_top : (Kakeya.realRpowENN δ cordobaLoss * ENNReal.ofReal radius * refinedDensity ^ 2 * bandCount * ENNReal.ofReal (δ ^ 2)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top h_rpowC_top h_ofRealRadius_top) h_rd2_top) h_bdcTop) h_ofRealD2_top
    have h := toReal_le_of_ennreal_le h_cordobaLHS_top h_tvTop h_cordoba
    rw [hLHS, hRHS] at h
    exact h
  -- Absorption condition
  have h_absorb' : 4 * Real.rpow 200 p * Real.rpow δ gap ≤ 1 := by
    simpa [hc_def] using h_absorb
  -- Apply Real-side core lemma
  have h_main : Real.rpow δ outputExponent * theta *
      Real.rpow ld (3 + p) * m ≤ tv :=
    real_hairbrush_hard_power_core zeta stemLoss bandLoss familyLoss hairLoss
      cordobaLoss outputExponent hzeta_pos hzeta_lt_one hstem hband hfamily
      hhair hcordoba hgap δ theta radius hδ hδ_lt_one htheta_pos htheta_le_one
      hradius_pos hradius_le_two ac hc rc bc bdc m ld hd rd tv
      h_pos1 h_pos2 h_pos3 h_pos4 h_pos5 h_pos6 h_pos7 h_pos8 h_pos9 h_pos10
      h_layer' h_hair_ret' h_family' h_ref_den' h_radius_den' h_stem' h_band'
      h_cordoba' h_absorb'
  -- Convert conclusion back to ENNReal
  set LHS_ENN : ENNReal := Kakeya.realRpowENN δ outputExponent *
      ENNReal.ofReal theta * layerDensity ^ (3 + p) * mu with hLHS_ENN_def
  have h3p_nonneg : 0 ≤ 3 + p := by linarith [hp_pos]
  have hLHS_top : LHS_ENN ≠ ⊤ := by
    rw [hLHS_ENN_def]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.ofReal_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg h3p_nonneg h_ldTop
    · exact h_muTop
  have hLHS_toReal : LHS_ENN.toReal =
      Real.rpow δ outputExponent * theta * Real.rpow ld (3 + p) * m := by
    have htheta_nonneg : 0 ≤ theta := by linarith
    have h1 : (layerDensity ^ (3 + p)).toReal = Real.rpow ld (3 + p) := by
      rw [toReal_rpow h_ld0 h_ldTop (3 + p)]
      <;> rfl
    simp [hLHS_ENN_def, toReal_mul, toReal_realRpowENN hδ, toReal_ofReal htheta_nonneg, h1, hm_def]
    <;> ring
  have h_final : LHS_ENN.toReal ≤ targetVolume.toReal := by
    rw [hLHS_toReal]
    have h_main2 : Real.rpow δ outputExponent * theta * Real.rpow ld (3 + p) * m ≤ targetVolume.toReal := by
      rw [htv_def] at h_main
      exact h_main
    exact h_main2
  have h_goal : LHS_ENN ≤ targetVolume :=
    (ENNReal.toReal_le_toReal hLHS_top h_tvTop).mp h_final
  simpa [hLHS_ENN_def, hp_def, hairbrushHomogeneousDensityPower] using h_goal

end Kakeya.Assouad
