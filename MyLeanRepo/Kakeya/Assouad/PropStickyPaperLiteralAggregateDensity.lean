import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralAggregateDensityStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-! # Aggregate density after literal unit rescaling -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_aggregate_density :
    WZ2PaperLiteralAggregateDensityStatement := by
  intro massUpper delta rho hdelta hrho hscale sourceFamily anchor
    familyData sourceShading shadingData imageMeasure sourceDensity
    lambda hSource hAbsorb
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho : ℝ) ^ 2)
  have hTargetMass :
      jacobian * sourceDensity * sourceFamily.enncard *
            Kakeya.realRpowENN delta 2 ≤
        shadingData.targetShading.mass := by
    calc
      jacobian * sourceDensity * sourceFamily.enncard *
            Kakeya.realRpowENN delta 2 =
          jacobian *
            (sourceDensity * sourceFamily.enncard *
              Kakeya.realRpowENN delta 2) := by
        ring
      _ ≤ jacobian * sourceShading.mass := by
        gcongr
      _ ≤ shadingData.targetShading.mass := by
        simpa [jacobian, mul_assoc] using
          imageMeasure.mass_lower
  have hCardinality :
      familyData.targetFamily.enncard =
        sourceFamily.enncard := by
    have hCard :
        familyData.targetFamily.card = sourceFamily.card := by
      simpa using
        Fintype.card_congr
        (Equiv.ofBijective
          familyData.sourceIndex
          familyData.sourceIndex_bijective)
    exact congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) hCard
  have hScaleIdentity :
      jacobian * Kakeya.realRpowENN delta 2 =
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          Kakeya.realRpowENN (delta / rho) 2 := by
    simp only [jacobian, Kakeya.realRpowENN]
    have hDelta :
        Real.rpow delta 2 = delta ^ 2 :=
      Real.rpow_natCast delta 2
    have hRatio :
        Real.rpow (delta / rho) 2 =
          (delta / rho) ^ 2 :=
      Real.rpow_natCast (delta / rho) 2
    rw [hDelta, hRatio]
    have hReal :
        (1 / rho : ℝ) ^ 2 * delta ^ 2 =
          (delta / rho) ^ 2 := by
      field_simp [hrho.ne']
    have hOfReal :
        ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
            ENNReal.ofReal (delta ^ 2) =
          ENNReal.ofReal ((delta / rho) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity), hReal]
    rw [mul_assoc, hOfReal]
  have hTargetLower :
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            sourceDensity) *
          Kakeya.realRpowENN (delta / rho) 2 *
          familyData.targetFamily.enncard ≤
        shadingData.targetShading.mass := by
    rw [hCardinality]
    calc
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            sourceDensity) *
          Kakeya.realRpowENN (delta / rho) 2 *
          sourceFamily.enncard =
        (jacobian * Kakeya.realRpowENN delta 2) *
          sourceDensity * sourceFamily.enncard := by
            rw [hScaleIdentity]
            ring
      _ =
        jacobian * sourceDensity * sourceFamily.enncard *
          Kakeya.realRpowENN delta 2 := by
            ring
      _ ≤ shadingData.targetShading.mass :=
        hTargetMass
  have hTargetBody :
      (wz1PaperBodyFamily familyData.targetFamily).mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
            familyData.targetFamily.enncard :=
    massUpper (div_pos hdelta hrho) hscale
      familyData.target_line_class
      { carrier := fun index =>
          wz1PaperTubeCarrier
            (familyData.targetFamily.tube index)
        measurable_carrier := fun index =>
          wz1PaperTubeCarrier_measurable
            (familyData.targetFamily.tube index)
        subset_body := fun _ => Set.Subset.rfl }
  have hAbsorbed :
      lambda *
            (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          familyData.targetFamily.enncard ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            sourceDensity) *
          Kakeya.realRpowENN (delta / rho) 2 *
          familyData.targetFamily.enncard := by
    calc
      lambda *
            (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
          familyData.targetFamily.enncard =
        (lambda * (55296 * Kakeya.deltaTubeVolume 1)) *
          (Kakeya.realRpowENN (delta / rho) 2 *
            familyData.targetFamily.enncard) := by
              ring
      _ ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            sourceDensity) *
          (Kakeya.realRpowENN (delta / rho) 2 *
            familyData.targetFamily.enncard) := by
              exact mul_le_mul_right' hAbsorb _
      _ =
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            sourceDensity) *
          Kakeya.realRpowENN (delta / rho) 2 *
          familyData.targetFamily.enncard := by
              ring
  calc
    lambda *
          (wz1PaperBodyFamily familyData.targetFamily).mass ≤
        lambda *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho) 2 *
              familyData.targetFamily.enncard) := by
      gcongr
    _ ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            sourceDensity) *
          Kakeya.realRpowENN (delta / rho) 2 *
            familyData.targetFamily.enncard := by
      simpa [mul_assoc] using hAbsorbed
    _ ≤ shadingData.targetShading.mass :=
      hTargetLower

end Kakeya.Assouad

end
