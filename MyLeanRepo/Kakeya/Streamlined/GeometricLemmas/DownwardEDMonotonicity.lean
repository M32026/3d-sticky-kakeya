import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Downward monotonicity of essential distinctness under radius decrease

If two tubes are "strongly essentially distinct" at radius R (intersection volume
is at most `V_R / K` for a sufficiently large constant K), then they are
essentially distinct at any smaller radius r ≤ R.

The proof uses two simple facts:
1. Shrinking the radius can only decrease the intersection (monotonicity of
   `Metric.cthickening`).
2. The tube volume ratio `V_R / V_r` is bounded by a constant depending only
   on the ratio `R / r` (`deltaTubeVolume_ratio_bound`).

## Main results

- `essentiallyDistinct_of_strong_ed_downward`: strong ED at radius R implies
  ED at radius r ≤ R, when `K ≥ 2 * C_vol(R/r)`.
-/

noncomputable section

open MeasureTheory Metric Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.GeometricLemmas

/-- Shrinking the radius decreases the intersection volume. -/
lemma tube_intersection_volume_mono {R r : ℝ} (h_le : r ≤ R)
    (base1 base2 : Point3) (dir1 dir2 : Point3)
    (h1 : ‖dir1‖ = 1) (h2 : ‖dir2‖ = 1) :
    volume (({base := base1, direction := dir1, direction_unit := h1} : Kakeya.DeltaTube r).carrier ∩
            ({base := base2, direction := dir2, direction_unit := h2} : Kakeya.DeltaTube r).carrier) ≤
    volume (({base := base1, direction := dir1, direction_unit := h1} : Kakeya.DeltaTube R).carrier ∩
            ({base := base2, direction := dir2, direction_unit := h2} : Kakeya.DeltaTube R).carrier) := by
  have h_contain : ∀ (T : Kakeya.DeltaTube r),
      T.carrier ⊆ ({base := T.base, direction := T.direction, direction_unit := T.direction_unit} : Kakeya.DeltaTube R).carrier := by
    intro T
    exact Metric.cthickening_mono h_le (unitSegment T.base T.direction)
  let T_r : Kakeya.DeltaTube r := {base := base1, direction := dir1, direction_unit := h1}
  let U_r : Kakeya.DeltaTube r := {base := base2, direction := dir2, direction_unit := h2}
  let T_R : Kakeya.DeltaTube R := {base := base1, direction := dir1, direction_unit := h1}
  let U_R : Kakeya.DeltaTube R := {base := base2, direction := dir2, direction_unit := h2}
  have h2 : T_r.carrier ⊆ T_R.carrier := h_contain T_r
  have h3 : U_r.carrier ⊆ U_R.carrier := h_contain U_r
  have h4 : T_r.carrier ∩ U_r.carrier ⊆ T_R.carrier ∩ U_R.carrier :=
    Set.inter_subset_inter h2 h3
  exact measure_mono h4

/-- **Strong ED at larger radius implies ED at smaller radius**.

If the intersection volume at radius R is at most `V_R / K` and
`K ≥ 2 * C_vol` where `C_vol` bounds `V_R / V_r`, then the tubes are
essentially distinct at radius r.

This is a weaker form of full downward monotonicity. It suffices for
multiscale constructions where coarse-scale ED is established with a
large enough constant.
-/
lemma essentiallyDistinct_of_strong_ed_downward
    {R r : ℝ} (hr_pos : 0 < r) (hR_pos : 0 < R) (h_le : r ≤ R)
    (base1 base2 : Point3) (dir1 dir2 : Point3)
    (h1 : ‖dir1‖ = 1) (h2 : ‖dir2‖ = 1)
    (K C_vol : ENNReal)
    (hC_vol : Kakeya.deltaTubeVolume R ≤ C_vol * Kakeya.deltaTubeVolume r)
    (hK : 2 * C_vol ≤ K)
    (h_strong :
      volume (({base := base1, direction := dir1, direction_unit := h1} : Kakeya.DeltaTube R).carrier ∩
              ({base := base2, direction := dir2, direction_unit := h2} : Kakeya.DeltaTube R).carrier) ≤
      Kakeya.deltaTubeVolume R / K) :
    ({base := base1, direction := dir1, direction_unit := h1} : Kakeya.DeltaTube r).EssentiallyDistinct
      ({base := base2, direction := dir2, direction_unit := h2} : Kakeya.DeltaTube r) := by
  let T_r : Kakeya.DeltaTube r := {base := base1, direction := dir1, direction_unit := h1}
  let U_r : Kakeya.DeltaTube r := {base := base2, direction := dir2, direction_unit := h2}
  let T_R : Kakeya.DeltaTube R := {base := base1, direction := dir1, direction_unit := h1}
  let U_R : Kakeya.DeltaTube R := {base := base2, direction := dir2, direction_unit := h2}

  have hVr : T_r.volume = Kakeya.deltaTubeVolume r :=
    tube_volume_eq_deltaTubeVolume T_r
  have hVr2 : U_r.volume = Kakeya.deltaTubeVolume r :=
    tube_volume_eq_deltaTubeVolume U_r

  have h_inter_mono : volume (T_r.carrier ∩ U_r.carrier) ≤
      volume (T_R.carrier ∩ U_R.carrier) :=
    tube_intersection_volume_mono h_le base1 base2 dir1 dir2 h1 h2

  have hVR_pos : 0 < Kakeya.deltaTubeVolume R :=
    deltaTubeVolume_pos hR_pos

  have hK_ne_zero : K ≠ 0 := by
    by_contra hK0
    have hC0 : C_vol = 0 := by
      have h : 2 * C_vol ≤ 0 := by rw [hK0] at hK <;> exact hK
      simpa using h
    have hVR0 : Kakeya.deltaTubeVolume R ≤ 0 := by
      calc
        Kakeya.deltaTubeVolume R ≤ C_vol * Kakeya.deltaTubeVolume r := hC_vol
        _ = 0 := by rw [hC0] <;> simp
    exact not_le.mpr hVR_pos hVR0

  have h_main : volume (T_r.carrier ∩ U_r.carrier) ≤
      (2⁻¹ : ENNReal) * Kakeya.deltaTubeVolume r := by
    by_cases hK_top : K = ⊤
    · -- K = ⊤: intersection at R is 0, hence at r is 0
      have h0 : Kakeya.deltaTubeVolume R / K = 0 := by
        rw [hK_top] <;> simp
      have hR0 : volume (T_R.carrier ∩ U_R.carrier) = 0 := by
        exact le_zero_iff.mp (h_strong.trans_eq h0)
      have hr0 : volume (T_r.carrier ∩ U_r.carrier) = 0 := by
        exact le_zero_iff.mp (h_inter_mono.trans_eq hR0)
      rw [hr0] <;> simp
    · -- 0 < K < ⊤
      have h5 : C_vol ≤ (2⁻¹ : ENNReal) * K := by
        have h21 : (2⁻¹ : ENNReal) * 2 = 1 := by
          rw [ENNReal.inv_mul_cancel] <;> norm_num
        calc
          C_vol = 1 * C_vol := by simp
          _ = ((2⁻¹ : ENNReal) * 2) * C_vol := by rw [h21]
          _ = (2⁻¹ : ENNReal) * (2 * C_vol) := by rw [mul_assoc]
          _ ≤ (2⁻¹ : ENNReal) * K := by gcongr
      calc
        volume (T_r.carrier ∩ U_r.carrier)
          ≤ volume (T_R.carrier ∩ U_R.carrier) := h_inter_mono
        _ ≤ Kakeya.deltaTubeVolume R / K := h_strong
        _ ≤ (C_vol * Kakeya.deltaTubeVolume r) / K := by
          gcongr <;> exact hC_vol
        _ = C_vol * Kakeya.deltaTubeVolume r * K⁻¹ := by
          simp [div_eq_mul_inv, mul_assoc]
        _ = Kakeya.deltaTubeVolume r * (C_vol * K⁻¹) := by
          simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
        _ ≤ Kakeya.deltaTubeVolume r * ((2⁻¹ : ENNReal) * K * K⁻¹) := by
          gcongr <;> exact h5
        _ = Kakeya.deltaTubeVolume r * (2⁻¹ : ENNReal) := by
          have hKK : K * K⁻¹ = 1 := ENNReal.mul_inv_cancel hK_ne_zero hK_top
          have h_inner : (2⁻¹ : ENNReal) * K * K⁻¹ = (2⁻¹ : ENNReal) := by
            have h_assoc : (2⁻¹ : ENNReal) * K * K⁻¹ = (2⁻¹ : ENNReal) * (K * K⁻¹) := by
              rw [mul_assoc]
            rw [h_assoc, hKK] <;> simp
          rw [h_inner]
        _ = (2⁻¹ : ENNReal) * Kakeya.deltaTubeVolume r := by
          rw [mul_comm]

  have h_max : max T_r.volume U_r.volume = Kakeya.deltaTubeVolume r := by
    rw [hVr, hVr2] <;> simp

  dsimp only [Kakeya.DeltaTube.EssentiallyDistinct]
  rw [h_max]
  exact h_main

/-- Convenience version using `deltaTubeVolume_ratio_bound` to compute
`C_vol` from the ratio `A = R / r`. -/
lemma essentiallyDistinct_of_strong_ed_downward'
    {R r A : ℝ} (hr_pos : 0 < r) (hR_pos : 0 < R) (h_le : r ≤ R)
    (hA_pos : 0 < A) (hR_le_A : R ≤ A * r) (hR_le_one : R ≤ 1)
    (base1 base2 : Point3) (dir1 dir2 : Point3)
    (h1 : ‖dir1‖ = 1) (h2 : ‖dir2‖ = 1)
    (K : ENNReal)
    (hK : 2 * ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) ≤ K)
    (h_strong :
      volume (({base := base1, direction := dir1, direction_unit := h1} : Kakeya.DeltaTube R).carrier ∩
              ({base := base2, direction := dir2, direction_unit := h2} : Kakeya.DeltaTube R).carrier) ≤
      Kakeya.deltaTubeVolume R / K) :
    ({base := base1, direction := dir1, direction_unit := h1} : Kakeya.DeltaTube r).EssentiallyDistinct
      ({base := base2, direction := dir2, direction_unit := h2} : Kakeya.DeltaTube r) := by
  let C_vol : ENNReal :=
    ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2)
  have hC_vol : Kakeya.deltaTubeVolume R ≤ C_vol * Kakeya.deltaTubeVolume r :=
    deltaTubeVolume_ratio_bound hr_pos hR_pos h_le hR_le_A hA_pos hR_le_one
  exact essentiallyDistinct_of_strong_ed_downward
    hr_pos hR_pos h_le base1 base2 dir1 dir2 h1 h2 K C_vol hC_vol hK h_strong

end Kakeya.Streamlined.GeometricLemmas
