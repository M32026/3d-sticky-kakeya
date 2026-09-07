import MyLeanRepo.Kakeya.CV.Isoperimetric
import MyLeanRepo.Kakeya.CV.Isoperimetric.Statements
import MyLeanRepo.Kakeya.CV.Isoperimetric.AddHaarScalarFactor2D
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.MeasurabilitySetup
import MyLeanRepo.Kakeya.CV.UnitSphereHausdorffArea

open Set MeasureTheory
open scoped ENNReal MeasureTheory

namespace Kakeya.CV

private lemma euclideanHausdorffMeasure_two_eq_standardSurfaceArea3
    (s : Set (Point 3)) :
    (μHE[2] : Measure (Point 3)) s = standardSurfaceArea3 s := by
  have h_finrank2 : Module.finrank ℝ (Point 2) = 2 := by
    have h : Module.finrank ℝ (Point 2) = Fintype.card (Fin 2) :=
      finrank_euclideanSpace_fin
    rw [h]
    decide
  letI h_haar2 : (μH[2] : Measure (Point 2)).IsAddHaarMeasure := by
    have h_eq : (↑(Module.finrank ℝ (Point 2)) : ℝ) = 2 := by
      rw [h_finrank2]
      norm_num
    have h :
        (μH[(↑(Module.finrank ℝ (Point 2)) : ℝ)] :
          Measure (Point 2)).IsAddHaarMeasure :=
      MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := Point 2)
    simpa [h_eq] using h
  let c : NNReal :=
    MeasureTheory.Measure.addHaarScalarFactor
      (volume : Measure (Point 2)) μH[2]
  have hdef : (μHE[2] : Measure (Point 3)) = (c : ENNReal) • μH[2] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def 2
  have hc : (c : ENNReal) = ENNReal.ofReal (Real.pi / 4) := by
    have hmeasure :
        (volume : Measure (Point 2)) =
          ENNReal.ofReal (Real.pi / 4) • μH[2] :=
      Geometry.addHaarScalarFactor_twoDim_eq_pi_div_four
    have hmuhe : (μHE[2] : Measure (Point 2)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2
    have hdef2 : (μHE[2] : Measure (Point 2)) = (c : ENNReal) • μH[2] :=
      MeasureTheory.Measure.euclideanHausdorffMeasure_def 2
    have heq :
        ((c : ENNReal) • μH[2] : Measure (Point 2)) =
          ENNReal.ofReal (Real.pi / 4) • μH[2] := by
      calc
        ((c : ENNReal) • μH[2] : Measure (Point 2)) = μHE[2] := hdef2.symm
        _ = volume := hmuhe
        _ = ENNReal.ofReal (Real.pi / 4) • μH[2] := hmeasure
    have hball : μH[2] (Metric.ball (0 : Point 2) 1) = 4 := by
      have hupper := Geometry.hausdorff_twoDim_ball_le_four
      have hlower := Geometry.hausdorff_twoDim_ge_volume_scaled
        (Metric.ball (0 : Point 2) 1)
      have hvol : volume (Metric.ball (0 : Point 2) 1) = ENNReal.ofReal Real.pi := by
        simpa using EuclideanSpace.volume_ball_fin_two 0 1
      rw [hvol] at hlower
      have hprod :
          ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal Real.pi = 4 := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        have h : (4 / Real.pi) * Real.pi = 4 := by
          field_simp [Real.pi_ne_zero]
        rw [h]
        norm_cast
      rw [hprod] at hlower
      exact le_antisymm hupper hlower
    have heval := congrArg
      (fun m : Measure (Point 2) => m (Metric.ball 0 1)) heq
    simp only [Measure.smul_apply, hball] at heval
    exact (ENNReal.mul_left_inj (by norm_num : (4 : ENNReal) ≠ 0)
      (by norm_num : (4 : ENNReal) ≠ ⊤)).mp heval
  have h3_def :
      (μHE[2] : Measure (Point 3)) = (c : ENNReal) • μH[2] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def 2
  have h4 :
      (μHE[2] : Measure (Point 3)) s =
        ENNReal.ofReal (Real.pi / 4) * μH[2] s := by
    rw [h3_def, hc]
    rfl
  rw [h4]
  unfold standardSurfaceArea3 codimensionOneMeasure
  norm_num

theorem polynomial_region_isoperimetric_from_general :
    PolynomialRegionIsoperimetricStatement := by
  intro p a _ha hvol
  let B := polynomialSublevelInUnitBall p
  have hB_meas : MeasurableSet B := by
    exact Metric.isClosed_closedBall.measurableSet.inter
      (isClosed_le (polynomialValue_continuous p) continuous_const).measurableSet
  have hB_bdd : Bornology.IsBounded B :=
    Metric.isBounded_closedBall.subset inter_subset_left
  have hiso :=
    Geometry.isoperimetric 3 (by norm_num) B hB_meas hB_bdd
  set V : ENNReal := volume (unitBall 3)
  set x : ENNReal := ENNReal.ofReal a
  set H : ENNReal := (μHE[2] : Measure (Point 3)) (frontier B)
  have hvol' : volume B = x * V := by simpa [B, x, V] using hvol
  have hiso' : 27 * (volume B) ^ 2 * V ≤ H ^ 3 := by
    have h_eq :
        (3 : ENNReal) ^ 3 * (volume B) ^ (3 - 1) *
            volume (unitBall 3) =
          27 * (volume B) ^ 2 * V := by
      simp [V, pow_two]
      norm_num
    have hiso2 :
        (3 : ENNReal) ^ 3 * (volume B) ^ (3 - 1) *
            volume (unitBall 3) ≤
          H ^ 3 := by
      simpa [unitBall, H] using hiso
    rw [h_eq] at hiso2
    exact hiso2
  set L : ENNReal := 3 * x ^ (2 / 3 : ℝ) * V
  have hL3 : L ^ 3 = 27 * x ^ 2 * V ^ 3 := by
    have hxpow : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
      rw [← ENNReal.rpow_mul_natCast]
      norm_num
    simp only [L, mul_pow, hxpow]
    ring
  have h_eq2 : 27 * (volume B) ^ 2 * V = L ^ 3 := by
    rw [hvol', hL3]
    simp [pow_two, mul_assoc]
    ring
  rw [h_eq2] at hiso'
  have hroot : L ≤ H := by
    exact (ENNReal.pow_le_pow_left_iff (n := 3) (by decide)).mp hiso'
  have hsphere :
      (μHE[2] : Measure (Point 3)) (unitSphere 3) = 3 * V := by
    rw [euclideanHausdorffMeasure_two_eq_standardSurfaceArea3,
      unitSphere_standardArea_eq_three_mul_volume]
  have hmuhe :
      x ^ (2 / 3 : ℝ) *
          (μHE[2] : Measure (Point 3)) (unitSphere 3) ≤
        (μHE[2] : Measure (Point 3)) (frontier B) := by
    rw [hsphere]
    simpa [L, H, mul_assoc, mul_comm, mul_left_comm] using hroot
  rw [euclideanHausdorffMeasure_two_eq_standardSurfaceArea3,
    euclideanHausdorffMeasure_two_eq_standardSurfaceArea3] at hmuhe
  let c : ENNReal := ENNReal.ofReal (Real.pi / 4)
  have hc0 : c ≠ 0 := by positivity
  have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  change x ^ (2 / 3 : ℝ) * codimensionOneMeasure 3 (unitSphere 3) ≤
    codimensionOneMeasure 3 (frontier B)
  apply (ENNReal.mul_le_mul_iff_left hc0 hcTop).mp
  simpa [standardSurfaceArea3, c, mul_assoc, mul_comm, mul_left_comm] using hmuhe

end Kakeya.CV
