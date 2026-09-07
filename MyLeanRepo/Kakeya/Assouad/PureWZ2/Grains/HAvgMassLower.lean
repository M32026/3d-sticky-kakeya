import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureCWAToCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements

/-!
# h_avg mass lower bound

Proves the core mass lower bound for the coarse shading:
`coarseShading.mass ≥ (1/4) * L^(2*loss)`

Uses:
1. CWA cardinality floor: `V * N ≥ L^loss / 4`
2. Paper carrier volume lower bound: `paperBodyMass ≥ V * N`
3. IsLambdaDense: `shading.mass ≥ L^loss * paperBodyMass`
4. Combining: `shading.mass ≥ L^(2*loss) / 4`
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set ENNReal

private lemma realRpowENN_add {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Kakeya.realRpowENN x (a + b) =
      Kakeya.realRpowENN x a * Kakeya.realRpowENN x b := by
  simp only [Kakeya.realRpowENN]
  have hreal : Real.rpow x (a + b) = Real.rpow x a * Real.rpow x b :=
    Real.rpow_add hx a b
  rw [hreal]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg hx.le a)

/-- Core mass lower bound using only the paper line-class input needed for the
carrier-volume estimate.  In particular, no Section 6 parent cover is needed. -/
lemma coarse_shading_mass_lower_bound_of_line_class
    {sigma loss L : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma loss coarse coarseShading)
    (hline : WZ1PaperIsLineClass coarse)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 24) :
    (1 / 4 : ENNReal) * Kakeya.realRpowENN L (2 * loss) ≤ coarseShading.mass := by
  have hnonempty : coarse.Nonempty := coarseExtremal.nonempty

  -- Step 1: CWA cardinality floor
  let C : ENNReal := Kakeya.realRpowENN L (-loss)
  have hcwa : WZ2PaperPureCWAAtNearbyScales coarse C :=
    coarseExtremal.cwa_nearby_scales
  have hcard : (1 : ENNReal) ≤ (4 : ENNReal) * C * Kakeya.deltaTubeVolume L * coarse.enncard :=
    pure_cwa_to_cardinality_floor hcwa hL_pos hL_small hnonempty

  have hC_ne_zero : C ≠ 0 := by
    simp [C, Kakeya.realRpowENN] <;> positivity
  have hC_ne_top : C ≠ ⊤ := by
    simp [C, Kakeya.realRpowENN]

  -- Step 2: Rearrange cardinality bound: V * N ≥ (1/4) * C⁻¹ = (1/4) * L^loss
  have h1 : C * (Kakeya.deltaTubeVolume L * coarse.enncard) ≥ (1 / 4 : ENNReal) := by
    have h2 : (1 : ENNReal) ≤ (4 : ENNReal) * (C * (Kakeya.deltaTubeVolume L * coarse.enncard)) := by
      simpa [mul_assoc] using hcard
    have h3 : (4 : ENNReal)⁻¹ * (1 : ENNReal) ≤
        (4 : ENNReal)⁻¹ * ((4 : ENNReal) * (C * (Kakeya.deltaTubeVolume L * coarse.enncard))) := by
      gcongr <;> exact h2
    have h4 : (4 : ENNReal)⁻¹ * ((4 : ENNReal) * (C * (Kakeya.deltaTubeVolume L * coarse.enncard))) =
        C * (Kakeya.deltaTubeVolume L * coarse.enncard) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
    have h5 : (4 : ENNReal)⁻¹ * (1 : ENNReal) = (1 / 4 : ENNReal) := by
      simp [one_div]
    rw [h5] at h3
    rw [h4] at h3
    exact h3

  have h1' : Kakeya.deltaTubeVolume L * coarse.enncard ≥
      (1 / 4 : ENNReal) * C⁻¹ := by
    have h4 : C⁻¹ * (C * (Kakeya.deltaTubeVolume L * coarse.enncard)) ≥
        C⁻¹ * (1 / 4 : ENNReal) := by gcongr <;> exact h1
    have h5 : C⁻¹ * (C * (Kakeya.deltaTubeVolume L * coarse.enncard)) =
        Kakeya.deltaTubeVolume L * coarse.enncard := by
      have h51 : C⁻¹ * (C * (Kakeya.deltaTubeVolume L * coarse.enncard)) =
          (C⁻¹ * C) * (Kakeya.deltaTubeVolume L * coarse.enncard) := by ring
      rw [h51]
      have h52 : C⁻¹ * C = 1 := ENNReal.inv_mul_cancel hC_ne_zero hC_ne_top
      rw [h52, one_mul]
    have h6 : C⁻¹ * (1 / 4 : ENNReal) = (1 / 4 : ENNReal) * C⁻¹ := by ring
    rw [h5] at h4
    rw [h6] at h4
    exact h4

  have hC_inv : C⁻¹ = Kakeya.realRpowENN L loss := by
    have h_pos : 0 < Real.rpow L (-loss) := Real.rpow_pos_of_pos hL_pos _
    have h_neg : Real.rpow L (-loss) = (Real.rpow L loss)⁻¹ :=
      Real.rpow_neg hL_pos.le loss
    have h_eq : (Real.rpow L (-loss))⁻¹ = Real.rpow L loss := by
      rw [h_neg]
      have h_pos2 : 0 < Real.rpow L loss := Real.rpow_pos_of_pos hL_pos _
      field_simp [h_pos2.ne']
    have h_main : (ENNReal.ofReal (Real.rpow L (-loss)))⁻¹ =
        ENNReal.ofReal (Real.rpow L loss) := by
      have h2 : ENNReal.ofReal ((Real.rpow L (-loss))⁻¹) =
          (ENNReal.ofReal (Real.rpow L (-loss)))⁻¹ :=
        ENNReal.ofReal_inv_of_pos h_pos
      have h3 : (ENNReal.ofReal (Real.rpow L (-loss)))⁻¹ =
          ENNReal.ofReal ((Real.rpow L (-loss))⁻¹) := h2.symm
      rw [h3, h_eq]
    simpa [C, Kakeya.realRpowENN] using h_main
  rw [hC_inv] at h1'

  -- Step 3: Paper body mass ≥ N * V
  have hpaper_mass : (coarse.enncard : ENNReal) * Kakeya.deltaTubeVolume L ≤
      (wz1PaperBodyFamily coarse).mass := by
    have h4 : ∀ (i : Fin coarse.card),
        Kakeya.deltaTubeVolume L ≤ volume (wz1PaperTubeCarrier (coarse.tube i)) := by
      intro i
      have hL_small12 : L ≤ 1 / 12 := by linarith
      exact wz2PaperTubeCarrier_volume_lower hL_pos hL_small12 (coarse.tube i) (hline i)
    have h_sum : ∑ i : Fin coarse.card, Kakeya.deltaTubeVolume L ≤
        ∑ i : Fin coarse.card, volume (wz1PaperTubeCarrier (coarse.tube i)) := by
      apply Finset.sum_le_sum; intro i _; exact h4 i
    have h_eq1 : (coarse.enncard : ENNReal) * Kakeya.deltaTubeVolume L =
        ∑ i : Fin coarse.card, Kakeya.deltaTubeVolume L := by
      have h : ∑ i : Fin coarse.card, Kakeya.deltaTubeVolume L =
          (Finset.card (Finset.univ : Finset (Fin coarse.card)) : ENNReal) * Kakeya.deltaTubeVolume L := by
        rw [Finset.sum_const] <;> simp
      have hcard : (Finset.card (Finset.univ : Finset (Fin coarse.card)) : ENNReal) = coarse.enncard := by
        have h1 : Finset.card (Finset.univ : Finset (Fin coarse.card)) = coarse.card := by
          simp
        rw [h1] <;> rfl
      rw [h, hcard] <;> ring
    have h_eq2 : (wz1PaperBodyFamily coarse).mass =
        ∑ i : Fin coarse.card, volume (wz1PaperTubeCarrier (coarse.tube i)) := by rfl
    rw [h_eq1, h_eq2]
    exact h_sum

  -- Step 4: Density: shading.mass ≥ L^loss * paperBodyMass
  have hdense : (Kakeya.realRpowENN L loss) * (wz1PaperBodyFamily coarse).mass ≤
      coarseShading.mass := coarseExtremal.dense

  -- Step 5: Combine
  have h_comm : (coarse.enncard : ENNReal) * Kakeya.deltaTubeVolume L =
      Kakeya.deltaTubeVolume L * coarse.enncard := by ring

  have h5 : (Kakeya.realRpowENN L loss) * (Kakeya.deltaTubeVolume L * coarse.enncard) ≤
      coarseShading.mass := by
    calc
      (Kakeya.realRpowENN L loss) * (Kakeya.deltaTubeVolume L * coarse.enncard)
        = (Kakeya.realRpowENN L loss) * ((coarse.enncard : ENNReal) * Kakeya.deltaTubeVolume L) := by
          rw [h_comm]
      _ ≤ (Kakeya.realRpowENN L loss) * (wz1PaperBodyFamily coarse).mass := by
          gcongr <;> exact hpaper_mass
      _ ≤ coarseShading.mass := hdense

  have h7 : (Kakeya.realRpowENN L loss) * (Kakeya.deltaTubeVolume L * coarse.enncard) ≥
      (Kakeya.realRpowENN L loss) * ((1 / 4 : ENNReal) * Kakeya.realRpowENN L loss) := by
    gcongr <;> exact h1'

  have h9 : Kakeya.realRpowENN L loss * Kakeya.realRpowENN L loss =
      Kakeya.realRpowENN L (2 * loss) := by
    have h91 : Kakeya.realRpowENN L loss * Kakeya.realRpowENN L loss =
        Kakeya.realRpowENN L (loss + loss) := (realRpowENN_add hL_pos loss loss).symm
    have h92 : loss + loss = 2 * loss := by ring
    rw [h91, h92]
  have h8 : (Kakeya.realRpowENN L loss) * ((1 / 4 : ENNReal) * Kakeya.realRpowENN L loss) =
      (1 / 4 : ENNReal) * Kakeya.realRpowENN L (2 * loss) := by
    calc
      (Kakeya.realRpowENN L loss) * ((1 / 4 : ENNReal) * Kakeya.realRpowENN L loss)
        = (1 / 4 : ENNReal) * (Kakeya.realRpowENN L loss * Kakeya.realRpowENN L loss) := by ring
      _ = (1 / 4 : ENNReal) * Kakeya.realRpowENN L (2 * loss) := by rw [h9]

  rw [h8] at h7
  exact h7.trans h5

/-- Backwards-compatible Section 6 wrapper around the direct line-class mass
lower bound. -/
lemma coarse_shading_mass_lower_bound
    {sigma loss L delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (coarseExtremal : WZ2PaperCroppedIsExtremal sigma loss coarse coarseShading)
    (cover : PureWZ2Section6Cover fine coarse)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 24) :
    (1 / 4 : ENNReal) * Kakeya.realRpowENN L (2 * loss) ≤ coarseShading.mass :=
  coarse_shading_mass_lower_bound_of_line_class
    coarseExtremal cover.coarse_line_class hL_pos hL_small

end Kakeya.Assouad

end
