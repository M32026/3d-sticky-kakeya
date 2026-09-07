import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Horizontal component bound in WZ1 Lemma 23

At the end of Lemma 23 Step 1, the local-grain normal is unit, has vertical
component at most `1/2`, and is nearly orthogonal to `(-slope, 1, 0)` while
the normalized global slope is small.  These facts force the first horizontal
component to be bounded away from zero.  This is the algebraic input used to
form the quotient defining the local graph.
-/

namespace Kakeya.Assouad

/--
The paper-safe numerical implication used at every selected coarse cell.
-/
theorem wz1_lemma23_normal_first_component
    (normal : Point3) (slope : ℝ)
    (hnorm : ‖normal‖ = 1)
    (hvertical : |normal (2 : Fin 3)| ≤ 1 / 2)
    (hslope : |slope| ≤ 1 / 10)
    (htilt :
      |normal (1 : Fin 3) -
          slope * normal (0 : Fin 3)| ≤ 1 / 10) :
    1 / 4 ≤ |normal (0 : Fin 3)| := by
  have hcoord :
      ∀ i : Fin 3, |normal i| ≤ 1 := by
    intro i
    have h :=
      PiLp.norm_apply_le normal i
    simpa [Real.norm_eq_abs, hnorm] using h
  have hsecond :
      |normal (1 : Fin 3)| ≤ 1 / 5 := by
    calc
      |normal (1 : Fin 3)|
          = |(normal (1 : Fin 3) -
                slope * normal (0 : Fin 3)) +
              slope * normal (0 : Fin 3)| := by ring
      _ ≤
          |normal (1 : Fin 3) -
              slope * normal (0 : Fin 3)| +
            |slope * normal (0 : Fin 3)| :=
        abs_add_le _ _
      _ ≤
          (1 / 10 : ℝ) +
            |slope| * |normal (0 : Fin 3)| := by
        rw [abs_mul]
        gcongr
      _ ≤ (1 / 10 : ℝ) + (1 / 10) * 1 := by
        gcongr
        exact hcoord 0
      _ = 1 / 5 := by norm_num
  have hnormSq :
      normal (0 : Fin 3) ^ 2 +
          normal (1 : Fin 3) ^ 2 +
          normal (2 : Fin 3) ^ 2 =
        1 := by
    have hsq :
        ‖normal‖ ^ 2 =
          ∑ i : Fin 3, normal i ^ 2 :=
      EuclideanSpace.real_norm_sq_eq normal
    rw [hnorm] at hsq
    simpa [Fin.sum_univ_succ, add_assoc] using hsq.symm
  have hsecondSq :
      normal (1 : Fin 3) ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := by
    nlinarith [sq_abs (normal (1 : Fin 3)),
      abs_nonneg (normal (1 : Fin 3))]
  have hverticalSq :
      normal (2 : Fin 3) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_abs (normal (2 : Fin 3)),
      abs_nonneg (normal (2 : Fin 3))]
  have hfirstSq :
      (1 / 4 : ℝ) ^ 2 ≤ normal (0 : Fin 3) ^ 2 := by
    nlinarith
  nlinarith [sq_abs (normal (0 : Fin 3)),
    abs_nonneg (normal (0 : Fin 3))]

/--
The generalized numerical implication with the source-package slope bound
`3` and the tightened tilt bound `1 / 14`.
-/
theorem wz1_lemma23_normal_first_component_generalized
    (normal : Point3) (slope : ℝ)
    (hnorm : ‖normal‖ = 1)
    (hvertical : |normal (2 : Fin 3)| ≤ 1 / 2)
    (hslope : |slope| ≤ 3)
    (htilt :
      |normal (1 : Fin 3) -
          slope * normal (0 : Fin 3)| ≤ 1 / 14) :
    1 / 4 ≤ |normal (0 : Fin 3)| := by
  set a := normal (0 : Fin 3) with ha_def
  set b := normal (1 : Fin 3) with hb_def
  set c := normal (2 : Fin 3) with hc_def
  set m := slope with hm_def
  have hnormSq : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
    have hsq : ‖normal‖ ^ 2 = ∑ i : Fin 3, normal i ^ 2 :=
      EuclideanSpace.real_norm_sq_eq normal
    rw [hnorm] at hsq
    simpa [Fin.sum_univ_succ, add_assoc, ha_def, hb_def, hc_def] using hsq.symm
  have hcSq : c ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_abs c, abs_nonneg c]
  have hhoriz : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 := by
    nlinarith
  by_contra h
  have h' : |a| < 1 / 4 := by linarith
  have hb_bound : |b| < 23 / 28 := by
    calc
      |b| = |(b - m * a) + m * a| := by rw [sub_add_cancel]
      _ ≤ |b - m * a| + |m * a| := abs_add_le _ _
      _ = |b - m * a| + |m| * |a| := by rw [abs_mul]
      _ ≤ 1 / 14 + 3 * |a| := by gcongr <;> linarith
      _ < 1 / 14 + 3 * (1 / 4 : ℝ) := by gcongr
      _ = 23 / 28 := by norm_num
  have hbSq : b ^ 2 < (23 / 28 : ℝ) ^ 2 := by
    have hpos : 0 ≤ |b| := abs_nonneg b
    have hsq : |b| ^ 2 < (23 / 28 : ℝ) ^ 2 := by
      gcongr <;> linarith
    simpa [sq_abs b] using hsq
  have haSq : a ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    have hpos : 0 ≤ |a| := abs_nonneg a
    have hsq : |a| ^ 2 < (1 / 4 : ℝ) ^ 2 := by
      gcongr <;> linarith
    simpa [sq_abs a] using hsq
  have hcont : a ^ 2 + b ^ 2 < 3 / 4 := by
    have harith :
        (1 / 4 : ℝ) ^ 2 + (23 / 28 : ℝ) ^ 2 < 3 / 4 := by
      norm_num
    linarith
  linarith [hhoriz]

end Kakeya.Assouad
