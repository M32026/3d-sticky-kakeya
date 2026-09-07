import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalTiltStatements

/-!
# Planar strip geometry for WZ1 Lemma 23 Step 1

A slice in one `sqrt rho` coarse square and one width-`rho` localCoord-projection
strip has global-grain projection inside an interval whose radius is controlled
by the tilt between the two projection directions.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The horizontal part of a unit normal has squared norm at least `3/4`. -/
private lemma normal_horizontal_sq_lower
    {normal : Point3}
    (hnorm : ‖normal‖ = 1)
    (hvertical : |normal (2 : Fin 3)| ≤ 1 / 2) :
    (3 / 4 : ℝ) ≤
      normal 0 ^ 2 + normal 1 ^ 2 := by
  have hsq :
      ‖normal‖ ^ 2 = ∑ i : Fin 3, normal i ^ 2 :=
    EuclideanSpace.real_norm_sq_eq normal
  rw [hnorm] at hsq
  have hsum :
      ∑ i : Fin 3, normal i ^ 2 =
        normal 0 ^ 2 + normal 1 ^ 2 + normal 2 ^ 2 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum] at hsq
  have hzsq : normal 2 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_abs (normal 2), abs_nonneg (normal 2)]
  nlinarith

/-- Every global projection lies in the tilt-controlled interval. -/
theorem WZ1Lemma23NormalTiltWitness.globalProjection_sub
    {rho sigma eta : ℝ} {C : ENNReal}
    {slope : ℝ → ℝ} {normal : Point3}
    (witness :
      WZ1Lemma23NormalTiltWitness
        rho sigma eta C slope normal)
    (hrho : 0 < rho) :
    witness.globalProjection ⊆
      witness.projected ∩
        Metric.closedBall
          witness.projectionCenter witness.projectionRadius := by
  intro value hvalue
  refine ⟨witness.globalProjection_sub_projected hvalue, ?_⟩
  rw [witness.globalProjection_eq] at hvalue
  rcases hvalue with ⟨point, hpoint, rfl⟩
  let dx := point 0 - witness.sliceCenter 0
  let dy := point 1 - witness.sliceCenter 1
  let a := normal 0
  let b := normal 1
  let m := slope witness.sliceHeight
  let localCoord :=
    a * point 0 + b * point 1 - witness.stripCenter
  let cross := a * dy - b * dx
  let tilt := b - m * a
  let projectionCenter :=
    ((a + m * b) * witness.stripCenter -
        tilt *
          (a * witness.sliceCenter 1 -
            b * witness.sliceCenter 0)) /
      (a ^ 2 + b ^ 2)
  have hcoords := witness.slice_in_square point hpoint
  have hlocal : |localCoord| ≤ rho := by
    simpa [localCoord, a, b] using
      witness.slice_in_local_strip point hpoint
  have ha : |a| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (0 : Fin 3)
    simpa [a, Real.norm_eq_abs, witness.normal_unit] using h
  have hb : |b| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (1 : Fin 3)
    simpa [b, Real.norm_eq_abs, witness.normal_unit] using h
  have hm : |m| ≤ 1 / 10 := witness.slope_small
  have hcross : |cross| ≤ 2 * Real.sqrt rho := by
    calc
      |cross| = |a * dy - b * dx| := rfl
      _ ≤ |a * dy| + |b * dx| := abs_sub _ _
      _ = |a| * |dy| + |b| * |dx| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * Real.sqrt rho + 1 * Real.sqrt rho := by
        gcongr
        · simpa [dy] using hcoords.2
        · simpa [dx] using hcoords.1
      _ = 2 * Real.sqrt rho := by ring
  have hcoef : |a + m * b| ≤ 2 := by
    calc
      |a + m * b| ≤ |a| + |m * b| := abs_add_le _ _
      _ = |a| + |m| * |b| := by rw [abs_mul]
      _ ≤ 1 + (1 / 10 : ℝ) * 1 := by gcongr
      _ ≤ 2 := by norm_num
  have hhorizontal :
      (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 := by
    simpa [a, b] using
      normal_horizontal_sq_lower
        witness.normal_unit witness.normal_vertical
  have hidentity :
      (a ^ 2 + b ^ 2) *
          ((point 0 + m * point 1) - projectionCenter) =
        (a + m * b) * localCoord - tilt * cross := by
    have hden : a ^ 2 + b ^ 2 ≠ 0 := by
      nlinarith
    dsimp only [projectionCenter, localCoord, cross, tilt, dx, dy]
    field_simp [hden]
    <;> ring
  have hscaled :
      (a ^ 2 + b ^ 2) *
          |(point 0 + m * point 1) - projectionCenter| ≤
        2 * rho +
          2 * Real.sqrt rho * |tilt| := by
    have hsqNonneg : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    rw [← abs_of_nonneg hsqNonneg, ← abs_mul, hidentity]
    have hsum :
        |(a + m * b) * localCoord - tilt * cross| ≤
          |a + m * b| * |localCoord| +
            |tilt| * |cross| := by
      calc
        |(a + m * b) * localCoord - tilt * cross|
            ≤ |(a + m * b) * localCoord| +
                |tilt * cross| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul]
    calc
      |(a + m * b) * localCoord - tilt * cross|
          ≤ |a + m * b| * |localCoord| +
              |tilt| * |cross| := hsum
      _ ≤ 2 * rho +
          |tilt| * (2 * Real.sqrt rho) := by gcongr
      _ = 2 * rho +
          2 * Real.sqrt rho * |tilt| := by ring
  have hprojection :
      |(point 0 + m * point 1) - projectionCenter| ≤
        4 * rho +
          4 * Real.sqrt rho * |tilt| := by
    have hnonneg :
        0 ≤ |(point 0 + m * point 1) - projectionCenter| :=
      abs_nonneg _
    have hquarter :
        (3 / 4 : ℝ) *
            |(point 0 + m * point 1) - projectionCenter| ≤
          2 * rho + 2 * Real.sqrt rho * |tilt| :=
      (mul_le_mul_of_nonneg_right
        hhorizontal hnonneg).trans hscaled
    have hrhs :
        2 * rho + 2 * Real.sqrt rho * |tilt| ≤
          (3 / 4 : ℝ) *
            (4 * rho + 4 * Real.sqrt rho * |tilt|) := by
      have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
      have htilt : 0 ≤ |tilt| := abs_nonneg _
      nlinarith
    nlinarith
  rw [Metric.mem_closedBall, Real.dist_eq,
    witness.projectionCenter_eq,
    witness.projectionRadius_eq]
  simpa [projectionCenter, a, b, m, tilt] using hprojection

/-- Every generalized global projection lies in its tilt-controlled interval. -/
theorem WZ1Lemma23NormalTiltWitnessGeneralized.globalProjection_sub
    {rho sigma eta : ℝ} {C : ENNReal}
    {slope : ℝ → ℝ} {normal : Point3}
    (witness :
      WZ1Lemma23NormalTiltWitnessGeneralized
        rho sigma eta C slope normal)
    (hrho : 0 < rho) :
    witness.globalProjection ⊆
      witness.projected ∩
        Metric.closedBall
          witness.projectionCenter witness.projectionRadius := by
  intro value hvalue
  refine ⟨witness.globalProjection_sub_projected hvalue, ?_⟩
  rw [witness.globalProjection_eq] at hvalue
  rcases hvalue with ⟨point, hpoint, rfl⟩
  let dx := point 0 - witness.sliceCenter 0
  let dy := point 1 - witness.sliceCenter 1
  let a := normal 0
  let b := normal 1
  let m := slope witness.sliceHeight
  let localCoord :=
    a * point 0 + b * point 1 - witness.stripCenter
  let cross := a * dy - b * dx
  let tilt := b - m * a
  let projectionCenter :=
    ((a + m * b) * witness.stripCenter -
        tilt *
          (a * witness.sliceCenter 1 -
            b * witness.sliceCenter 0)) /
      (a ^ 2 + b ^ 2)
  have hcoords := witness.slice_in_square point hpoint
  have hlocal : |localCoord| ≤ rho := by
    simpa [localCoord, a, b] using
      witness.slice_in_local_strip point hpoint
  have ha : |a| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (0 : Fin 3)
    simpa [a, Real.norm_eq_abs, witness.normal_unit] using h
  have hb : |b| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (1 : Fin 3)
    simpa [b, Real.norm_eq_abs, witness.normal_unit] using h
  have hm : |m| ≤ 3 := witness.slope_small
  have htilt_lower : Real.sqrt rho ≤ |tilt| := witness.tilt_lower
  have hcross : |cross| ≤ 2 * Real.sqrt rho := by
    calc
      |cross| = |a * dy - b * dx| := rfl
      _ ≤ |a * dy| + |b * dx| := abs_sub _ _
      _ = |a| * |dy| + |b| * |dx| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * Real.sqrt rho + 1 * Real.sqrt rho := by
        gcongr
        · simpa [dy] using hcoords.2
        · simpa [dx] using hcoords.1
      _ = 2 * Real.sqrt rho := by ring
  have hcoef : |a + m * b| ≤ 4 := by
    calc
      |a + m * b| ≤ |a| + |m * b| := abs_add_le _ _
      _ = |a| + |m| * |b| := by rw [abs_mul]
      _ ≤ 1 + (3 : ℝ) * 1 := by gcongr
      _ ≤ 4 := by norm_num
  have hhorizontal :
      (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 := by
    simpa [a, b] using
      normal_horizontal_sq_lower
        witness.normal_unit witness.normal_vertical
  have hidentity :
      (a ^ 2 + b ^ 2) *
          ((point 0 + m * point 1) - projectionCenter) =
        (a + m * b) * localCoord - tilt * cross := by
    have hden : a ^ 2 + b ^ 2 ≠ 0 := by
      nlinarith
    dsimp only [projectionCenter, localCoord, cross, tilt, dx, dy]
    field_simp [hden]
    <;> ring
  have hscaled :
      (a ^ 2 + b ^ 2) *
          |(point 0 + m * point 1) - projectionCenter| ≤
        4 * rho + 2 * Real.sqrt rho * |tilt| := by
    have hsqNonneg : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    rw [← abs_of_nonneg hsqNonneg, ← abs_mul, hidentity]
    have hsum :
        |(a + m * b) * localCoord - tilt * cross| ≤
          |a + m * b| * |localCoord| +
            |tilt| * |cross| := by
      calc
        |(a + m * b) * localCoord - tilt * cross|
            ≤ |(a + m * b) * localCoord| +
                |tilt * cross| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_mul]
    calc
      |(a + m * b) * localCoord - tilt * cross|
          ≤ |a + m * b| * |localCoord| +
              |tilt| * |cross| := hsum
      _ ≤ 4 * rho + |tilt| * (2 * Real.sqrt rho) := by
        gcongr
      _ = 4 * rho + 2 * Real.sqrt rho * |tilt| := by ring
  have hprojection :
      |(point 0 + m * point 1) - projectionCenter| ≤
        4 * rho + 4 * Real.sqrt rho * |tilt| := by
    have hnonneg :
        0 ≤ |(point 0 + m * point 1) - projectionCenter| :=
      abs_nonneg _
    have hquarter :
        (3 / 4 : ℝ) *
            |(point 0 + m * point 1) - projectionCenter| ≤
          4 * rho + 2 * Real.sqrt rho * |tilt| :=
      (mul_le_mul_of_nonneg_right
        hhorizontal hnonneg).trans hscaled
    have hrho_le : rho ≤ Real.sqrt rho * |tilt| := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
      have hmul :
          Real.sqrt rho * Real.sqrt rho ≤
            Real.sqrt rho * |tilt| :=
        mul_le_mul_of_nonneg_left htilt_lower hsqrt_nonneg
      have hsq : Real.sqrt rho ^ 2 = rho :=
        Real.sq_sqrt hrho.le
      nlinarith
    have hrhs :
        4 * rho + 2 * Real.sqrt rho * |tilt| ≤
          (3 / 4 : ℝ) *
            (4 * rho + 4 * Real.sqrt rho * |tilt|) := by
      have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
      have htilt : 0 ≤ |tilt| := abs_nonneg _
      nlinarith [hrho_le]
    nlinarith
  rw [Metric.mem_closedBall, Real.dist_eq,
    witness.projectionCenter_eq,
    witness.projectionRadius_eq]
  simpa [projectionCenter, a, b, m, tilt] using hprojection

/-- The chosen radius directly dominates the tilt scale. -/
theorem WZ1Lemma23NormalTiltWitness.tilt_radius
    {rho sigma eta : ℝ} {C : ENNReal}
    {slope : ℝ → ℝ} {normal : Point3}
    (witness :
      WZ1Lemma23NormalTiltWitness
        rho sigma eta C slope normal)
    (hrho : 0 < rho) :
    Real.sqrt rho *
        |normal (1 : Fin 3) -
          slope witness.sliceHeight * normal (0 : Fin 3)| ≤
      witness.projectionRadius := by
  rw [witness.projectionRadius_eq]
  have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have htilt :
      0 ≤ |normal 1 -
        slope witness.sliceHeight * normal 0| := abs_nonneg _
  nlinarith

/-- The chosen generalized radius directly dominates the tilt scale. -/
theorem WZ1Lemma23NormalTiltWitnessGeneralized.tilt_radius
    {rho sigma eta : ℝ} {C : ENNReal}
    {slope : ℝ → ℝ} {normal : Point3}
    (witness :
      WZ1Lemma23NormalTiltWitnessGeneralized
        rho sigma eta C slope normal)
    (hrho : 0 < rho) :
    Real.sqrt rho *
        |normal (1 : Fin 3) -
          slope witness.sliceHeight * normal (0 : Fin 3)| ≤
      witness.projectionRadius := by
  rw [witness.projectionRadius_eq]
  have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have htilt :
      0 ≤ |normal 1 -
        slope witness.sliceHeight * normal 0| := abs_nonneg _
  nlinarith

end

end Kakeya.Assouad
