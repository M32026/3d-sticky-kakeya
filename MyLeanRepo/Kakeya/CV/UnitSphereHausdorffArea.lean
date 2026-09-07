import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Isoperimetric.SphereProjection
import MyLeanRepo.Kakeya.CV.Isoperimetric.AddHaarScalarFactor2D
import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory Metric Set
open scoped ENNReal

/-!
# Hausdorff area of the three-dimensional unit sphere

The normalization identity required to convert the inner-Minkowski
isoperimetric constant into the CV boundary-area normalization.

Proof route:
1. `standardSurfaceArea3(s) = ENNReal.ofReal(π/4) * μH[2](s)` by definition.
2. Determine the scalar factor `c = addHaarScalarFactor(volume, μH[2])` by working
   on `Point 2`: there `μHE[2] = volume = (π/4) • μH[2]`, and evaluating on the
   unit ball gives `c = π/4`.
3. On `Point 3`, `μHE[2] = c • μH[2] = (π/4) • μH[2]`, so
   `standardSurfaceArea3(sphere) = μHE[2](sphere)`.
4. `μHE[2](sphere) = volume.toSphere univ` by `muHE_two_sphere_eq_toSphere`.
5. `volume.toSphere univ = 3 * volume(ball 0 1)` by `toSphere_apply_univ`.
6. `volume(ball 0 1) = volume(unitBall 3)` since the sphere boundary has measure zero.
-/

namespace Kakeya.CV

open scoped MeasureTheory

theorem unitSphere_standardArea_eq_three_mul_volume :
    standardSurfaceArea3 (unitSphere 3) =
      (3 : ℝ≥0∞) * volume (unitBall 3) := by
  have h_finrank2 : Module.finrank ℝ (Point 2) = 2 := by
    have h : Module.finrank ℝ (Point 2) = Fintype.card (Fin 2) := finrank_euclideanSpace_fin
    rw [h] <;> decide
  letI h_haar2 : (μH[2] : Measure (Point 2)).IsAddHaarMeasure := by
    have h_eq : (↑(Module.finrank ℝ (Point 2)) : ℝ) = 2 := by
      rw [h_finrank2] <;> norm_num
    have h : (μH[(↑(Module.finrank ℝ (Point 2)) : ℝ)] : Measure (Point 2)).IsAddHaarMeasure :=
      MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := Point 2)
    simpa [h_eq] using h

  let c : NNReal := MeasureTheory.Measure.addHaarScalarFactor (volume : Measure (Point 2)) μH[2]

  have h2d_def : (μHE[2] : Measure (Point 2)) = (c : ENNReal) • μH[2] := by
    have h := MeasureTheory.Measure.euclideanHausdorffMeasure_def (d := 2) (X := Point 2)
    simpa [c, Measure.smul_apply] using h

  have h2d_vol : (μHE[2] : Measure (Point 2)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2
  have h2d_factor : (volume : Measure (Point 2)) = ENNReal.ofReal (Real.pi / 4) • μH[2] :=
    Geometry.addHaarScalarFactor_twoDim_eq_pi_div_four

  have h_upper : μH[2] (ball (0 : Point 2) 1) ≤ 4 := Geometry.hausdorff_twoDim_ball_le_four
  have h_lower : (ENNReal.ofReal (4 / Real.pi)) * volume (ball (0 : Point 2) 1) ≤
      μH[2] (ball (0 : Point 2) 1) :=
    Geometry.hausdorff_twoDim_ge_volume_scaled (ball 0 1)
  have h_vol2 : volume (ball (0 : Point 2) 1) = ENNReal.ofReal Real.pi := by
    simpa using EuclideanSpace.volume_ball_fin_two 0 1
  have h_ball1 : μH[2] (ball (0 : Point 2) 1) = 4 := by
    rw [h_vol2] at h_lower
    have h3 : (ENNReal.ofReal (4 / Real.pi)) * ENNReal.ofReal Real.pi = 4 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h4 : (4 / Real.pi) * Real.pi = 4 := by
        field_simp [Real.pi_ne_zero] <;> ring
      rw [h4] <;> norm_cast
    rw [h3] at h_lower
    exact le_antisymm h_upper h_lower

  have h_eq : ((c : ENNReal) • μH[2] : Measure (Point 2)) =
      (ENNReal.ofReal (Real.pi / 4) • μH[2] : Measure (Point 2)) := by
    calc
      ((c : ENNReal) • μH[2] : Measure (Point 2))
          = (μHE[2] : Measure (Point 2)) := h2d_def.symm
      _ = (volume : Measure (Point 2)) := h2d_vol
      _ = (ENNReal.ofReal (Real.pi / 4) • μH[2] : Measure (Point 2)) := h2d_factor
  have h_eval : (c : ENNReal) * μH[2] (ball (0 : Point 2) 1) =
      ENNReal.ofReal (Real.pi / 4) * μH[2] (ball (0 : Point 2) 1) := by
    have h : ((c : ENNReal) • (μH[2] : Measure (Point 2))) (ball (0 : Point 2) 1) =
        (ENNReal.ofReal (Real.pi / 4) • (μH[2] : Measure (Point 2)))
          (ball (0 : Point 2) 1) := by
      rw [h_eq]
    simpa [Measure.smul_apply] using h
  have h_c : (c : ENNReal) = ENNReal.ofReal (Real.pi / 4) := by
    rw [h_ball1] at h_eval
    exact (ENNReal.mul_left_inj (by norm_num) (by norm_num)).mp h_eval

  have h1 : standardSurfaceArea3 (unitSphere 3) =
      ENNReal.ofReal (Real.pi / 4) * μH[2] (unitSphere 3) := by
    unfold standardSurfaceArea3 codimensionOneMeasure
    <;> norm_num

  have h3_def : (μHE[2] : Measure (Point 3)) = (c : ENNReal) • μH[2] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def 2
  have h4 : (μHE[2] : Measure (Point 3)) (unitSphere 3) =
      ENNReal.ofReal (Real.pi / 4) * μH[2] (unitSphere 3) := by
    rw [h3_def, h_c] <;> rfl

  have h5 : standardSurfaceArea3 (unitSphere 3) =
      (μHE[2] : Measure (Point 3)) (unitSphere 3) := by
    rw [h1, h4]

  have h6 : (μHE[2] : Measure (Point 3)) (unitSphere 3) =
      (volume : Measure (Point 3)).toSphere Set.univ :=
    muHE_two_sphere_eq_toSphere

  have h7 : (volume : Measure (Point 3)).toSphere Set.univ =
      (3 : ENNReal) * volume (ball (0 : Point 3) 1) := by
    have h := MeasureTheory.Measure.toSphere_apply_univ (μ := (volume : Measure (Point 3)))
    have h_fin : Module.finrank ℝ (Point 3) = 3 := by
      rw [finrank_euclideanSpace_fin] <;> decide
    rw [h, h_fin] <;> norm_num

  have h8 : volume (ball (0 : Point 3) 1) = volume (unitBall 3) := by
    have h_sub : ball (0 : Point 3) 1 ⊆ unitBall 3 := by
      intro x hx
      have h_dist : dist x 0 < 1 := by
        simpa [Metric.mem_ball] using hx
      simpa [unitBall, Metric.mem_closedBall] using h_dist.le
    have h_diff : (unitBall 3) \ ball (0 : Point 3) 1 ⊆ sphere (0 : Point 3) 1 := by
      intro x hx
      simpa [unitBall, Metric.mem_closedBall, Metric.mem_sphere] using hx
    have h_sphere_zero : volume (sphere (0 : Point 3) 1) = 0 :=
      MeasureTheory.Measure.addHaar_sphere volume 0 1
    have h_diff_zero : volume ((unitBall 3) \ ball (0 : Point 3) 1) = 0 :=
      measure_mono_null h_diff h_sphere_zero
    have h_eq : volume (unitBall 3) = volume (ball (0 : Point 3) 1) := by
      have h_union : (ball (0 : Point 3) 1) ∪
          ((unitBall 3) \ ball (0 : Point 3) 1) = unitBall 3 :=
        Set.union_diff_cancel h_sub
      have h9 : volume (unitBall 3) ≤ volume (ball (0 : Point 3) 1) := by
        rw [← h_union]
        calc
          volume ((ball (0 : Point 3) 1) ∪
              ((unitBall 3) \ ball (0 : Point 3) 1))
              ≤ volume (ball (0 : Point 3) 1) +
                  volume ((unitBall 3) \ ball (0 : Point 3) 1) :=
            measure_union_le _ _
          _ = volume (ball (0 : Point 3) 1) := by
            rw [h_diff_zero, add_zero]
      exact le_antisymm h9 (measure_mono h_sub)
    exact h_eq.symm

  calc
    standardSurfaceArea3 (unitSphere 3)
        = (μHE[2] : Measure (Point 3)) (unitSphere 3) := h5
    _ = (volume : Measure (Point 3)).toSphere Set.univ := h6
    _ = (3 : ENNReal) * volume (ball (0 : Point 3) 1) := h7
    _ = (3 : ENNReal) * volume (unitBall 3) := by rw [h8]

end Kakeya.CV
