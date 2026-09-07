import MyLeanRepo.Kakeya.Assouad.Subunit.AsymptoticHelper
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-side core algebra for homogeneous hard power
-/

namespace Kakeya.Assouad

lemma real_hairbrush_hard_power_core
    (zeta stemLoss bandLoss familyLoss hairLoss cordobaLoss outputExponent : ℝ)
    (hzeta_pos : 0 < zeta) (hzeta_lt_one : zeta < 1)
    (hstem : 0 ≤ stemLoss) (hband : 0 ≤ bandLoss)
    (hfamily : 0 ≤ familyLoss) (hhair : 0 ≤ hairLoss)
    (hcordoba : 0 ≤ cordobaLoss)
    (hgap : 1 + stemLoss + bandLoss + familyLoss + hairLoss + cordobaLoss < outputExponent)
    (δ theta radius : ℝ)
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (htheta_pos : 0 < theta) (htheta_le_one : theta ≤ 1)
    (hradius_pos : 0 < radius) (hradius_le_two : radius ≤ 2)
    (ambientCount hairCount refinedCount brushCount bandCount mu
     layerDensity hairDensity refinedDensity targetVolume : ℝ)
    (h_pos1 : 0 < ambientCount) (h_pos2 : 0 < hairCount)
    (h_pos3 : 0 < refinedCount) (h_pos4 : 0 < brushCount)
    (h_pos5 : 0 < bandCount) (h_pos6 : 0 < mu)
    (h_pos7 : 0 < layerDensity) (h_pos8 : 0 < hairDensity)
    (h_pos9 : 0 < refinedDensity) (h_pos10 : 0 ≤ targetVolume)
    (h_layer : layerDensity / 2 ≤ hairDensity)
    (h_hair_ret : Real.rpow δ hairLoss * layerDensity * ambientCount ≤ hairDensity * hairCount)
    (h_family : Real.rpow δ familyLoss * hairCount ≤ refinedCount)
    (h_ref_den : Real.rpow radius zeta * hairDensity ≤ refinedDensity)
    (h_radius_den : hairDensity ≤ 100 * Real.rpow radius (1 - zeta))
    (h_stem : Real.rpow δ stemLoss * theta * mu * refinedDensity * refinedCount / (δ * ambientCount) ≤ brushCount)
    (h_band : Real.rpow δ bandLoss * brushCount ≤ bandCount)
    (h_cordoba : Real.rpow δ cordobaLoss * radius * refinedDensity^2 * bandCount * δ^2 ≤ targetVolume)
    (h_absorb : 4 * Real.rpow 200 (((1 + 3 * zeta) / (1 - zeta))) *
                  Real.rpow δ (outputExponent - (1 + stemLoss + bandLoss + familyLoss + hairLoss + cordobaLoss)) ≤ 1) :
    Real.rpow δ outputExponent * theta *
      Real.rpow layerDensity (3 + (1 + 3 * zeta) / (1 - zeta)) * mu ≤ targetVolume := by
  set p : ℝ := (1 + 3 * zeta) / (1 - zeta) with hp_def
  set total : ℝ := 1 + stemLoss + bandLoss + familyLoss + hairLoss + cordobaLoss with htotal_def
  set gap : ℝ := outputExponent - total with hgap_def
  set ac := ambientCount with hac_def
  set hc := hairCount with hhc_def
  set rc := refinedCount with hrc_def
  set bc := brushCount with hbc_def
  set bdc := bandCount with hbdc_def
  set m := mu with hm_def
  set ld := layerDensity with hld_def
  set hd := hairDensity with hhd_def
  set rd := refinedDensity with hrd_def
  set tv := targetVolume with htv_def
  set dC := Real.rpow δ cordobaLoss with hdC_def
  set dB := Real.rpow δ bandLoss with hdB_def
  set dS := Real.rpow δ stemLoss with hdS_def
  set dF := Real.rpow δ familyLoss with hdF_def
  set dH := Real.rpow δ hairLoss with hdH_def
  set dTotal := Real.rpow δ total with hdTotal_def
  set dGap := Real.rpow δ gap with hdGap_def
  set dOut := Real.rpow δ outputExponent with hdOut_def
  set rζ := Real.rpow radius zeta with hrζ_def
  set r13ζ := Real.rpow radius (1 + 3 * zeta) with hr13ζ_def

  have h_ac_ne : ac ≠ 0 := h_pos1.ne'
  have h_hd_ne : hd ≠ 0 := h_pos8.ne'
  have hD_nonneg : ∀ (x : ℝ), 0 ≤ Real.rpow δ x := fun x => Real.rpow_nonneg hδ_pos.le x

  have hp_pos : 0 < p := by
    have h1 : 0 < 1 + 3 * zeta := by linarith
    have h2 : 0 < 1 - zeta := by linarith
    exact div_pos h1 h2
  have hp_exp : (1 - zeta) * p = 1 + 3 * zeta := by
    rw [hp_def]
    field_simp [show (1 - zeta : ℝ) ≠ 0 by linarith] <;> ring
  have hgap_pos : 0 < gap := by rw [hgap_def] <;> linarith

  have h_add : ∀ (x y : ℝ), Real.rpow δ x * Real.rpow δ y = Real.rpow δ (x + y) := by
    intro x y
    exact (Real.rpow_add hδ_pos x y).symm

  have h_r13 : r13ζ = radius * rζ^3 := by
    simp only [r13ζ, rζ]
    have h21 : Real.rpow radius zeta * Real.rpow radius zeta = Real.rpow radius (2 * zeta) := by
      have h : Real.rpow radius (zeta + zeta) = Real.rpow radius zeta * Real.rpow radius zeta :=
        Real.rpow_add hradius_pos zeta zeta
      have h' : zeta + zeta = 2 * zeta := by ring
      rw [h'] at h
      exact h.symm
    have h22 : Real.rpow radius (2 * zeta) * Real.rpow radius zeta = Real.rpow radius (3 * zeta) := by
      have h : Real.rpow radius (2 * zeta + zeta) = Real.rpow radius (2 * zeta) * Real.rpow radius zeta :=
        Real.rpow_add hradius_pos (2 * zeta) zeta
      have h' : 2 * zeta + zeta = 3 * zeta := by ring
      rw [h'] at h
      exact h.symm
    have h1 : (Real.rpow radius zeta)^3 = Real.rpow radius (3 * zeta) := by
      calc
        (Real.rpow radius zeta)^3
          = Real.rpow radius zeta * Real.rpow radius zeta * Real.rpow radius zeta := by ring
        _ = Real.rpow radius (2 * zeta) * Real.rpow radius zeta := by rw [h21]
        _ = Real.rpow radius (3 * zeta) := by rw [h22]
    have h2 : Real.rpow radius (1 + 3 * zeta) = radius * Real.rpow radius (3 * zeta) := by
      have h : Real.rpow radius (1 + 3 * zeta) = Real.rpow radius 1 * Real.rpow radius (3 * zeta) :=
        Real.rpow_add hradius_pos 1 (3 * zeta)
      have h_rpow1 : Real.rpow radius 1 = radius := by simp
      rw [h, h_rpow1] <;> ring
    rw [h1]
    exact h2

  have h_mul1 : ∀ (x : ℝ), Real.rpow δ x * δ = Real.rpow δ (x + 1) := by
    intro x
    have h : Real.rpow δ (x + 1) = Real.rpow δ x * Real.rpow δ 1 := Real.rpow_add hδ_pos x 1
    have h1 : Real.rpow δ 1 = δ := by simp
    rw [h1] at h
    exact h.symm

  have h_dTotal : dTotal = dC * dB * dS * δ * dF * dH := by
    have h1 : dC * dB = Real.rpow δ (cordobaLoss + bandLoss) := h_add cordobaLoss bandLoss
    have h2 : (dC * dB) * dS = Real.rpow δ (cordobaLoss + bandLoss + stemLoss) := by
      rw [h1]; exact h_add (cordobaLoss + bandLoss) stemLoss
    have h3 : ((dC * dB) * dS) * δ = Real.rpow δ (cordobaLoss + bandLoss + stemLoss + 1) := by
      rw [h2]; exact h_mul1 (cordobaLoss + bandLoss + stemLoss)
    have h4 : (((dC * dB) * dS) * δ) * dF = Real.rpow δ (cordobaLoss + bandLoss + stemLoss + 1 + familyLoss) := by
      rw [h3]; exact h_add (cordobaLoss + bandLoss + stemLoss + 1) familyLoss
    have h5 : ((((dC * dB) * dS) * δ) * dF) * dH = Real.rpow δ (cordobaLoss + bandLoss + stemLoss + 1 + familyLoss + hairLoss) := by
      rw [h4]; exact h_add (cordobaLoss + bandLoss + stemLoss + 1 + familyLoss) hairLoss
    have h6 : ((((dC * dB) * dS) * δ) * dF) * dH = dC * dB * dS * δ * dF * dH := by ring
    have h7 : cordobaLoss + bandLoss + stemLoss + 1 + familyLoss + hairLoss = total := by
      simp [htotal_def] <;> ring
    have h8 : dC * dB * dS * δ * dF * dH = Real.rpow δ total := by
      rw [← h6, h5, h7] <;> rfl
    exact h8.symm

  have h_dOut : dOut = dTotal * dGap := by
    simp only [dOut, dTotal, dGap]
    have h : Real.rpow δ (total + gap) = Real.rpow δ total * Real.rpow δ gap :=
      Real.rpow_add hδ_pos total gap
    have h' : total + gap = outputExponent := by simp [hgap_def] <;> ring
    rw [h'] at h
    exact h

  -- Step 1: bandCount substitution
  have h1 : dC * radius * rd^2 * (dB * bc) * δ^2 ≤ tv := by
    have hctx : 0 ≤ dC * radius * rd^2 * δ^2 := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact hD_nonneg cordobaLoss
          · exact hradius_pos.le
        · exact sq_nonneg rd
      · exact sq_nonneg δ
    have h : dC * radius * rd^2 * δ^2 * (dB * bc) ≤ dC * radius * rd^2 * δ^2 * bdc :=
      mul_le_mul_of_nonneg_left h_band hctx
    have h_eq1 : dC * radius * rd^2 * (dB * bc) * δ^2 = dC * radius * rd^2 * δ^2 * (dB * bc) := by ring
    have h_cordoba' : dC * radius * rd^2 * δ^2 * bdc ≤ tv := by
      have h_eq2 : dC * radius * rd^2 * bdc * δ^2 = dC * radius * rd^2 * δ^2 * bdc := by ring
      rw [h_eq2] at h_cordoba
      exact h_cordoba
    rw [h_eq1]
    exact le_trans h h_cordoba'

  -- Step 2: brushCount substitution
  have h2 : dC * dB * dS * radius * rd^3 * theta * m * rc * δ / ac ≤ tv := by
    have hpos_ac : 0 < δ * ac := mul_pos hδ_pos h_pos1
    have hctx2 : 0 ≤ dC * radius * rd^2 * δ^2 := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · exact hD_nonneg cordobaLoss
          · exact hradius_pos.le
        · exact sq_nonneg rd
      · exact sq_nonneg δ
    have h_stem_mul : dS * theta * m * rd * rc ≤ bc * (δ * ac) := by
      have h_eq : dS * theta * m * rd * rc = (dS * theta * m * rd * rc / (δ * ac)) * (δ * ac) := by
        field_simp [hpos_ac.ne'] <;> ring
      rw [h_eq]
      gcongr
    have h : dC * radius * rd^2 * δ^2 * (dB * (dS * theta * m * rd * rc / (δ * ac))) ≤
        dC * radius * rd^2 * δ^2 * (dB * bc) := by
      have hinner : dB * (dS * theta * m * rd * rc / (δ * ac)) ≤ dB * bc :=
        mul_le_mul_of_nonneg_left h_stem (hD_nonneg bandLoss)
      exact mul_le_mul_of_nonneg_left hinner hctx2
    have h_main : dC * radius * rd^2 * (dB * (dS * theta * m * rd * rc / (δ * ac))) * δ^2 ≤ tv := by
      have h_eq : dC * radius * rd^2 * (dB * (dS * theta * m * rd * rc / (δ * ac))) * δ^2 =
          dC * radius * rd^2 * δ^2 * (dB * (dS * theta * m * rd * rc / (δ * ac))) := by ring
      rw [h_eq]
      exact le_trans h (by simpa [mul_assoc, mul_comm, mul_left_comm] using h1)
    have h_final_eq : dC * dB * dS * radius * rd^3 * theta * m * rc * δ / ac =
        dC * radius * rd^2 * (dB * (dS * theta * m * rd * rc / (δ * ac))) * δ^2 := by
      field_simp [hpos_ac.ne'] <;> ring
    rw [h_final_eq]
    exact h_main

  -- Step 3: refinedCount substitution
  have h3 : dC * dB * dS * dF * radius * rd^3 * theta * m * hc * δ / ac ≤ tv := by
    let C3 := dC * dB * dS * radius * rd^3 * theta * m * δ / ac
    have h_dC_nonneg : 0 ≤ dC := hD_nonneg cordobaLoss
    have h_dB_nonneg : 0 ≤ dB := hD_nonneg bandLoss
    have h_dS_nonneg : 0 ≤ dS := hD_nonneg stemLoss
    have hctx3 : 0 ≤ C3 := by
      dsimp only [C3]
      have hnum : 0 ≤ dC * dB * dS * radius * rd^3 * theta * m * δ := by
        have h1 : 0 ≤ dC := hD_nonneg cordobaLoss
        have h2 : 0 ≤ dB := hD_nonneg bandLoss
        have h3 : 0 ≤ dS := hD_nonneg stemLoss
        have h4 : 0 ≤ radius := hradius_pos.le
        have h5 : 0 ≤ rd^3 := by positivity
        have h6 : 0 ≤ theta := htheta_pos.le
        have h7 : 0 ≤ m := h_pos6.le
        have h8 : 0 ≤ δ := hδ_pos.le
        positivity
      exact div_nonneg hnum h_pos1.le
    have h_sub : C3 * (dF * hc) ≤ C3 * rc := mul_le_mul_of_nonneg_left h_family hctx3
    have h_eq1 : C3 * (dF * hc) = dC * dB * dS * dF * radius * rd^3 * theta * m * hc * δ / ac := by
      dsimp only [C3] <;> ring
    have h_eq2 : C3 * rc = dC * dB * dS * radius * rd^3 * theta * m * rc * δ / ac := by
      dsimp only [C3] <;> ring
    rw [h_eq1, h_eq2] at h_sub
    exact le_trans h_sub h2

  -- Step 4: refinedDensity substitution
  have h4 : dC * dB * dS * dF * r13ζ * hd^3 * theta * m * hc * δ / ac ≤ tv := by
    let C4 := dC * dB * dS * dF * theta * m * hc * δ / ac
    have hnum4 : 0 ≤ dC * dB * dS * dF * theta * m * hc * δ := by
      have h1 : 0 ≤ dC := hD_nonneg cordobaLoss
      have h2 : 0 ≤ dB := hD_nonneg bandLoss
      have h3 : 0 ≤ dS := hD_nonneg stemLoss
      have h4' : 0 ≤ dF := hD_nonneg familyLoss
      positivity
    have hctx4 : 0 ≤ C4 := by
      dsimp only [C4]
      exact div_nonneg hnum4 h_pos1.le
    have h_rd3 : (rζ * hd)^3 ≤ rd^3 := by
      have h8 : rζ * hd ≤ rd := h_ref_den
      have h9 : 0 ≤ rζ * hd := by
        apply mul_nonneg
        · exact Real.rpow_nonneg hradius_pos.le zeta
        · exact h_pos8.le
      have h10 : 0 ≤ rd := h_pos9.le
      have h11 : (rζ * hd)^2 ≤ rd^2 := by
        calc (rζ * hd)^2
          = (rζ * hd) * (rζ * hd) := by ring
        _ ≤ rd * (rζ * hd) := by gcongr
        _ ≤ rd * rd := by gcongr
        _ = rd^2 := by ring
      calc (rζ * hd)^3
        = (rζ * hd)^2 * (rζ * hd) := by ring
      _ ≤ rd^2 * (rζ * hd) := by gcongr
      _ ≤ rd^2 * rd := by gcongr
      _ = rd^3 := by ring
    have h_rd3_radius : radius * (rζ * hd)^3 ≤ radius * rd^3 :=
      mul_le_mul_of_nonneg_left h_rd3 hradius_pos.le
    have h_sub : C4 * (radius * (rζ * hd)^3) ≤ C4 * (radius * rd^3) :=
      mul_le_mul_of_nonneg_left h_rd3_radius hctx4
    have h_eq1 : C4 * (radius * (rζ * hd)^3) = dC * dB * dS * dF * r13ζ * hd^3 * theta * m * hc * δ / ac := by
      dsimp only [C4]
      have h_r : radius * (rζ * hd)^3 = r13ζ * hd^3 := by
        rw [h_r13] <;> ring
      rw [h_r] <;> ring
    have h_eq2 : C4 * (radius * rd^3) = dC * dB * dS * dF * radius * rd^3 * theta * m * hc * δ / ac := by
      dsimp only [C4] <;> ring
    rw [h_eq1, h_eq2] at h_sub
    exact le_trans h_sub h3

  -- Step 5: hairCount substitution
  have h5 : dTotal * r13ζ * hd^2 * theta * m * ld ≤ tv := by
    let C5 := dC * dB * dS * dF * r13ζ * hd^3 * theta * m * δ
    have hnum5 : 0 ≤ C5 := by
      dsimp only [C5]
      have h1 : 0 ≤ dC := hD_nonneg cordobaLoss
      have h2 : 0 ≤ dB := hD_nonneg bandLoss
      have h3 : 0 ≤ dS := hD_nonneg stemLoss
      have h4' : 0 ≤ dF := hD_nonneg familyLoss
      have h5' : 0 ≤ r13ζ := Real.rpow_nonneg hradius_pos.le (1 + 3 * zeta)
      positivity
    have h_pos_hd_ac : 0 < hd * ac := mul_pos h_pos8 h_pos1
    have h_div : dH * ld / hd ≤ hc / ac := by
      have h : dH * ld * ac ≤ hd * hc := h_hair_ret
      have h' : (dH * ld * ac) / (hd * ac) ≤ (hd * hc) / (hd * ac) :=
        div_le_div_of_nonneg_right h (by positivity)
      have h9 : dH * ld / hd = (dH * ld * ac) / (hd * ac) := by
        field_simp [h_hd_ne, h_ac_ne] <;> ring
      have h10 : (hd * hc) / (hd * ac) = hc / ac := by
        field_simp [h_hd_ne, h_ac_ne] <;> ring
      rw [h9]
      rw [h10] at h'
      exact h'
    have h_sub : C5 * (dH * ld / hd) ≤ C5 * (hc / ac) :=
      mul_le_mul_of_nonneg_left h_div hnum5
    have h_eq1 : C5 * (dH * ld / hd) = dC * dB * dS * dF * dH * r13ζ * hd^2 * theta * m * ld * δ := by
      dsimp only [C5]
      field_simp [h_hd_ne] <;> ring
    have h_eq2 : C5 * (hc / ac) = dC * dB * dS * dF * r13ζ * hd^3 * theta * m * hc * δ / ac := by
      dsimp only [C5]
      <;> ring
    rw [h_eq1, h_eq2] at h_sub
    have h_dTotal_eq : dC * dB * dS * dF * dH * r13ζ * hd^2 * theta * m * ld * δ =
        dTotal * r13ζ * hd^2 * theta * m * ld := by
      rw [h_dTotal] <;> ring
    rw [h_dTotal_eq] at h_sub
    exact le_trans h_sub h4

  -- Key inequality: dGap * ld^(3+p) ≤ r13ζ * hd^2 * ld
  have h_ld_bound : ld ≤ 200 * Real.rpow radius (1 - zeta) := by
    have h1 : ld ≤ 2 * hd := by linarith
    have h2 : 2 * hd ≤ 200 * Real.rpow radius (1 - zeta) := by
      calc 2 * hd ≤ 2 * (100 * Real.rpow radius (1 - zeta)) := by gcongr
        _ = 200 * Real.rpow radius (1 - zeta) := by ring
    linarith
  have h_ld_p : Real.rpow ld p ≤ Real.rpow 200 p * r13ζ := by
    have h1 : Real.rpow ld p ≤ Real.rpow (200 * Real.rpow radius (1 - zeta)) p :=
      Real.rpow_le_rpow (by linarith) h_ld_bound hp_pos.le
    have h2 : Real.rpow (200 * Real.rpow radius (1 - zeta)) p =
        Real.rpow 200 p * Real.rpow radius ((1 - zeta) * p) := by
      have h_pos1 : 0 ≤ (200 : ℝ) := by norm_num
      have h_pos2 : 0 ≤ Real.rpow radius (1 - zeta) := Real.rpow_nonneg hradius_pos.le (1 - zeta)
      have h_mul : ((200 * Real.rpow radius (1 - zeta)) ^ p) = (200 : ℝ) ^ p * (Real.rpow radius (1 - zeta)) ^ p :=
        Real.mul_rpow (z := p) h_pos1 h_pos2
      have h_rpow_mul : (Real.rpow radius (1 - zeta)) ^ p = Real.rpow radius ((1 - zeta) * p) :=
        (Real.rpow_mul hradius_pos.le (1 - zeta) p).symm
      have h_left : Real.rpow (200 * Real.rpow radius (1 - zeta)) p = ((200 * Real.rpow radius (1 - zeta)) ^ p) := by rfl
      have h_right : (200 : ℝ) ^ p * (Real.rpow radius (1 - zeta)) ^ p = Real.rpow 200 p * Real.rpow radius ((1 - zeta) * p) := by
        have h1 : (200 : ℝ) ^ p = Real.rpow 200 p := by rfl
        rw [h1, h_rpow_mul] <;> rfl
      rw [h_left, h_mul, h_right]
    rw [h2, hp_exp] at h1
    simpa [r13ζ] using h1
  have h_hd2_ld : ld^3 / 4 ≤ hd^2 * ld := by
    have h1 : (ld / 2)^2 ≤ hd^2 := by gcongr
    have h2 : (ld / 2)^2 = ld^2 / 4 := by ring
    rw [h2] at h1
    have h3 : ld^2 / 4 * ld ≤ hd^2 * ld := by
      gcongr
      <;> exact h_pos7.le
    have h4 : ld^2 / 4 * ld = ld^3 / 4 := by ring
    rw [h4] at h3
    exact h3
  have h_absorb' : dGap * Real.rpow 200 p ≤ 1 / 4 := by
    have h : 4 * Real.rpow 200 p * dGap ≤ 1 := h_absorb
    have h' : dGap * Real.rpow 200 p = (4 * Real.rpow 200 p * dGap) / 4 := by ring
    rw [h']
    have h'' : (4 * Real.rpow 200 p * dGap) / 4 ≤ 1 / 4 := by
      gcongr
    exact h''
  have h_ld3p : Real.rpow ld (3 + p) = (ld^3 : ℝ) * Real.rpow ld p := by
    have h1 : Real.rpow ld (3 + p) = Real.rpow ld (3 : ℝ) * Real.rpow ld p :=
      Real.rpow_add h_pos7 3 p
    have h2 : Real.rpow ld (3 : ℝ) = (ld^3 : ℝ) := by simp
    rw [h1, h2]
  have h_r13ζ_nonneg : 0 ≤ r13ζ := Real.rpow_nonneg hradius_pos.le (1 + 3 * zeta)
  have h_key : dGap * Real.rpow ld (3 + p) ≤ r13ζ * hd^2 * ld := by
    have h_ctx : 0 ≤ dGap * (ld^3 : ℝ) := by
      apply mul_nonneg
      · exact hD_nonneg gap
      · positivity
    have h_step1 : dGap * (ld^3 : ℝ) * Real.rpow ld p ≤ dGap * (ld^3 : ℝ) * (Real.rpow 200 p * r13ζ) :=
      mul_le_mul_of_nonneg_left h_ld_p h_ctx
    have h_step2 : dGap * (ld^3 : ℝ) * (Real.rpow 200 p * r13ζ) = dGap * Real.rpow 200 p * (ld^3 : ℝ) * r13ζ := by ring
    have h_step3 : dGap * Real.rpow 200 p * (ld^3 : ℝ) * r13ζ ≤ (1 / 4 : ℝ) * (ld^3 : ℝ) * r13ζ := by
      have h_r13ζ_nonneg : 0 ≤ r13ζ := Real.rpow_nonneg hradius_pos.le (1 + 3 * zeta)
      have h_ctx2 : 0 ≤ (ld^3 : ℝ) * r13ζ := by
        apply mul_nonneg
        · positivity
        · exact h_r13ζ_nonneg
      have h : (ld^3 : ℝ) * r13ζ * (dGap * Real.rpow 200 p) ≤ (ld^3 : ℝ) * r13ζ * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left h_absorb' h_ctx2
      have h_eq : (ld^3 : ℝ) * r13ζ * (dGap * Real.rpow 200 p) = dGap * Real.rpow 200 p * (ld^3 : ℝ) * r13ζ := by ring
      have h_eq2 : (ld^3 : ℝ) * r13ζ * (1 / 4 : ℝ) = (1 / 4 : ℝ) * (ld^3 : ℝ) * r13ζ := by ring
      rw [h_eq, h_eq2] at h
      exact h
    calc
      dGap * Real.rpow ld (3 + p)
        = dGap * (ld^3 : ℝ) * Real.rpow ld p := by rw [h_ld3p] <;> ring
      _ ≤ dGap * (ld^3 : ℝ) * (Real.rpow 200 p * r13ζ) := h_step1
      _ = dGap * Real.rpow 200 p * (ld^3 : ℝ) * r13ζ := h_step2
      _ ≤ (1 / 4 : ℝ) * (ld^3 : ℝ) * r13ζ := h_step3
      _ = r13ζ * ((ld^3 : ℝ) / 4) := by ring
      _ ≤ r13ζ * (hd^2 * ld) := by
        exact mul_le_mul_of_nonneg_left h_hd2_ld h_r13ζ_nonneg
      _ = r13ζ * hd^2 * ld := by ring

  -- Final combine
  have h_goal : dOut * theta * Real.rpow ld (3 + p) * m ≤ tv := by
    rw [h_dOut]
    have h_ctx_final : 0 ≤ dTotal * theta * m := by
      apply mul_nonneg
      · apply mul_nonneg
        · exact hD_nonneg total
        · exact htheta_pos.le
      · exact h_pos6.le
    have h7 : dTotal * theta * m * (dGap * Real.rpow ld (3 + p)) ≤ dTotal * theta * m * (r13ζ * hd^2 * ld) :=
      mul_le_mul_of_nonneg_left h_key h_ctx_final
    have h7' : dTotal * dGap * theta * Real.rpow ld (3 + p) * m = dTotal * theta * m * (dGap * Real.rpow ld (3 + p)) := by ring
    have h8 : dTotal * theta * m * (r13ζ * hd^2 * ld) = dTotal * r13ζ * hd^2 * theta * m * ld := by ring
    rw [h7']
    rw [h8] at h7
    exact le_trans h7 h5
  exact h_goal

end Kakeya.Assouad
