import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Geometry.Euclidean.Angle.Unoriented.CrossProduct

/-!
# WZ1 cross-product perturbation

These lemmas transfer transversality and plane incidence from fine directions
to projectively aligned coarse directions.
-/

namespace Kakeya.Assouad

open Matrix

lemma wz1Cross_norm_le (u v : Point3) :
    ‖wz1Cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  let a : Fin 3 → ℝ := u
  let b : Fin 3 → ℝ := v
  let angle := InnerProductGeometry.angle
    (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  have hcross :
      ‖WithLp.toLp 2 (a ⨯₃ b)‖ =
        ‖WithLp.toLp 2 a‖ * ‖WithLp.toLp 2 b‖ * Real.sin angle :=
    InnerProductGeometry.norm_toLp_symm_crossProduct a b
  have hsin_nonneg : 0 ≤ Real.sin angle :=
    Real.sin_nonneg_of_mem_Icc
      ⟨InnerProductGeometry.angle_nonneg _ _,
        InnerProductGeometry.angle_le_pi _ _⟩
  have hsin_le : Real.sin angle ≤ 1 := Real.sin_le_one _
  have hpos : 0 ≤ ‖u‖ * ‖v‖ := by positivity
  have hmul :
      ‖u‖ * ‖v‖ * Real.sin angle ≤ ‖u‖ * ‖v‖ := by
    nlinarith
  calc
    ‖wz1Cross u v‖ = ‖WithLp.toLp 2 (a ⨯₃ b)‖ := rfl
    _ = ‖WithLp.toLp 2 a‖ * ‖WithLp.toLp 2 b‖ * Real.sin angle :=
      hcross
    _ = ‖u‖ * ‖v‖ * Real.sin angle := rfl
    _ ≤ ‖u‖ * ‖v‖ := hmul

lemma wz1Cross_add_left (a b c : Point3) :
    wz1Cross (a + b) c = wz1Cross a c + wz1Cross b c := by
  simp [wz1Cross, crossProduct.map_add]

lemma wz1Cross_add_right (a b c : Point3) :
    wz1Cross a (b + c) = wz1Cross a b + wz1Cross a c := by
  simp [wz1Cross, map_add]

lemma wz1Cross_smul_left (s : ℝ) (a b : Point3) :
    wz1Cross (s • a) b = s • wz1Cross a b := by
  simp [wz1Cross]

lemma wz1Cross_smul_right (s : ℝ) (a b : Point3) :
    wz1Cross a (s • b) = s • wz1Cross a b := by
  simp [wz1Cross]

/--
Projective direction errors of at most `4 * rho` per factor cost at most
`8 * rho` in cross-product transversality.
-/
lemma wz1Cross_perturbation
    (u1 u2 v1 v2 : Point3)
    (hu1 : ‖u1‖ = 1) (hu2 : ‖u2‖ = 1)
    (hv1 : ‖v1‖ = 1) (_hv2 : ‖v2‖ = 1)
    (s1 s2 : ℝ) (hs1 : s1 = 1 ∨ s1 = -1) (hs2 : s2 = 1 ∨ s2 = -1)
    (rho : ℝ) (_hrho : 0 ≤ rho)
    (h1 : ‖v1 - s1 • u1‖ ≤ 4 * rho)
    (h2 : ‖v2 - s2 • u2‖ ≤ 4 * rho)
    (fineKappa : ℝ)
    (hkappa : fineKappa ≤ ‖wz1Cross u1 u2‖) :
    fineKappa - 8 * rho ≤ ‖wz1Cross v1 v2‖ := by
  let e1 := v1 - s1 • u1
  let e2 := v2 - s2 • u2
  have hv1_eq : v1 = s1 • u1 + e1 := by simp [e1]
  have hv2_eq : v2 = s2 • u2 + e2 := by simp [e2]
  have hstep1 :
      wz1Cross v1 v2 =
        wz1Cross v1 e2 + s2 • wz1Cross v1 u2 := by
    rw [hv2_eq, wz1Cross_add_right, wz1Cross_smul_right]
    abel
  have hstep2 :
      wz1Cross v1 u2 =
        s1 • wz1Cross u1 u2 + wz1Cross e1 u2 := by
    rw [hv1_eq, wz1Cross_add_left, wz1Cross_smul_left]
  have hdecomp :
      wz1Cross v1 v2 =
        wz1Cross v1 e2 + s2 • wz1Cross e1 u2 +
          (s1 * s2) • wz1Cross u1 u2 := by
    rw [hstep1, hstep2, smul_add, smul_smul]
    simp only [mul_comm s2 s1]
    abel
  have habs1 : |s1| = 1 := by
    rcases hs1 with (rfl | rfl) <;> norm_num
  have habs2 : |s2| = 1 := by
    rcases hs2 with (rfl | rfl) <;> norm_num
  have hbound1 : ‖wz1Cross v1 e2‖ ≤ 4 * rho := by
    calc
      ‖wz1Cross v1 e2‖ ≤ ‖v1‖ * ‖e2‖ :=
        wz1Cross_norm_le v1 e2
      _ = ‖e2‖ := by rw [hv1]; ring
      _ ≤ 4 * rho := by simpa [e2] using h2
  have hbound2 : ‖s2 • wz1Cross e1 u2‖ ≤ 4 * rho := by
    rw [norm_smul, Real.norm_eq_abs, habs2, one_mul]
    calc
      ‖wz1Cross e1 u2‖ ≤ ‖e1‖ * ‖u2‖ :=
        wz1Cross_norm_le e1 u2
      _ = ‖e1‖ := by rw [hu2]; ring
      _ ≤ 4 * rho := by simpa [e1] using h1
  set x := wz1Cross v1 e2
  set y := s2 • wz1Cross e1 u2
  set z := (s1 * s2) • wz1Cross u1 u2
  have hdecomp' : wz1Cross v1 v2 = x + y + z := hdecomp
  have habs12 : |s1 * s2| = 1 := by
    rw [abs_mul, habs1, habs2]
    norm_num
  have hnormz : ‖z‖ = ‖wz1Cross u1 u2‖ := by
    rw [show z = (s1 * s2) • wz1Cross u1 u2 by rfl,
      norm_smul, Real.norm_eq_abs, habs12, one_mul]
  have hineq : ‖z‖ ≤ ‖wz1Cross v1 v2‖ + ‖x‖ + ‖y‖ := by
    have hz : z = wz1Cross v1 v2 - (x + y) := by
      rw [hdecomp']
      abel
    rw [hz]
    have hsub :
        ‖wz1Cross v1 v2 - (x + y)‖ ≤
          ‖wz1Cross v1 v2‖ + ‖x + y‖ :=
      norm_sub_le _ _
    have hadd : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
    linarith
  rw [hnormz] at hineq
  linarith [hkappa, hbound1, hbound2]

/--
Fine incidence at scale `rho` and projective alignment at scale `4 * rho`
give coarse incidence at scale `5 * rho`.
-/
lemma wz1Incidence_transfer
    (normal fineDir coarseDir : Point3)
    (hnormal : ‖normal‖ = 1)
    (rho : ℝ) (_hrho : 0 ≤ rho)
    (hfine : |inner ℝ fineDir normal| ≤ rho)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (halign : ‖coarseDir - sign • fineDir‖ ≤ 4 * rho) :
    |inner ℝ coarseDir normal| ≤ 5 * rho := by
  have hsign_abs : |sign| = 1 := by
    rcases hsign with (rfl | rfl) <;> norm_num
  have hinner :
      inner ℝ coarseDir normal =
        sign * inner ℝ fineDir normal +
          inner ℝ (coarseDir - sign • fineDir) normal := by
    have hsum :
        sign • fineDir + (coarseDir - sign • fineDir) = coarseDir := by
      abel
    rw [← hsum, inner_add_left, inner_smul_left]
    simp
  have herr :
      |inner ℝ (coarseDir - sign • fineDir) normal| ≤ 4 * rho := by
    calc
      |inner ℝ (coarseDir - sign • fineDir) normal|
          ≤ ‖coarseDir - sign • fineDir‖ * ‖normal‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖coarseDir - sign • fineDir‖ := by rw [hnormal]; ring
      _ ≤ 4 * rho := halign
  rw [hinner]
  have htriangle :
      |sign * inner ℝ fineDir normal +
          inner ℝ (coarseDir - sign • fineDir) normal| ≤
        |sign * inner ℝ fineDir normal| +
          |inner ℝ (coarseDir - sign • fineDir) normal| := by
    simpa [Real.norm_eq_abs] using
      norm_add_le (sign * inner ℝ fineDir normal)
        (inner ℝ (coarseDir - sign • fineDir) normal)
  have hsign_fine :
      |sign * inner ℝ fineDir normal| ≤ rho := by
    rw [abs_mul, hsign_abs, one_mul]
    exact hfine
  calc
    |sign * inner ℝ fineDir normal +
        inner ℝ (coarseDir - sign • fineDir) normal|
        ≤ |sign * inner ℝ fineDir normal| +
            |inner ℝ (coarseDir - sign • fineDir) normal| := htriangle
    _ ≤ rho + 4 * rho := add_le_add hsign_fine herr
    _ = 5 * rho := by ring

end Kakeya.Assouad
