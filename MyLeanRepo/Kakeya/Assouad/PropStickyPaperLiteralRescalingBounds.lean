import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Component and norm bounds for the WZ2 literal rescaling linear map

The WZ2 literal map is `(1/100) • unitRescalingMap ... rho ...`, i.e.
the linear part is `L v := (1/100) • unitRescalingLinear d hd rho v`.

This file establishes:
1. `(L v) 2 = (1/100) * inner ℝ v d`
2. `|(L v) 0| ≤ ‖P_perp(v)‖ / (100*rho)`
3. `|(L v) 1| ≤ ‖P_perp(v)‖ / (100*rho)`
4. `‖L v‖ ≤ ‖v‖ / (100*rho)` for `0 < rho ≤ 1`

where `P_perp(v) = v - inner ℝ v d • d`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The perpendicular projection of `v` onto the orthogonal complement of `d`. -/
def perpPart (d : Point3) (v : Point3) : Point3 :=
  v - inner ℝ v d • d

/-- Norm squared of the perpendicular part. -/
lemma perpPart_norm_sq {d : Point3} (hd : ‖d‖ = 1) (v : Point3) :
    ‖perpPart d v‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ v d) ^ 2 := by
  let a := inner ℝ v d
  let w := a • d
  have h_main : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2 :=
    norm_sub_sq_real v w
  have h2 : inner ℝ v w = a ^ 2 := by
    have h21 : inner ℝ v w = a * inner ℝ v d := by
      simp [w, inner_smul_right]
    rw [h21]
    have ha : a = inner ℝ v d := by rfl
    rw [ha] <;> ring
  have h3 : ‖w‖ ^ 2 = a ^ 2 := by
    have h4 : ‖w‖ = |a| * ‖d‖ := norm_smul a d
    have h5 : ‖w‖ ^ 2 = (|a| * ‖d‖) ^ 2 := by rw [h4]
    rw [h5, hd]
    have h6 : (|a| * (1 : ℝ)) ^ 2 = a ^ 2 := by
      simp [sq_abs]
    exact h6
  have h_goal : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - a ^ 2 := by
    rw [h_main, h2, h3] <;> ring
  have h_perp : perpPart d v = v - w := by
    have ha : a = inner ℝ v d := by rfl
    simp [perpPart, w, ha]
  rw [h_perp]
  exact h_goal

/-- The householder reflection preserves the norm of the perpendicular part. -/
lemma householder_transversePart_norm_eq_perpPart
    {d : Point3} (hd : ‖d‖ = 1) (v : Point3) :
    ‖transversePart (householderToE3 d hd v)‖ = ‖perpPart d v‖ := by
  set w := householderToE3 d hd v with hw
  have h1 : ‖transversePart w‖ ^ 2 = ‖w‖ ^ 2 - (w 2) ^ 2 :=
    transversePart_norm_sq w
  have h2 : ‖w‖ = ‖v‖ := householderToE3_norm d hd v
  have h3 : w 2 = inner ℝ v d := by
    rw [coord2_eq_inner_e3 w]
    rw [householderToE3_symmetric d hd v e3]
    rw [householderToE3_sends_e3_to_d d hd]
  have h5 : ‖transversePart w‖ ^ 2 = ‖perpPart d v‖ ^ 2 := by
    rw [h1, h2, h3, perpPart_norm_sq hd v]
  have h6 : 0 ≤ ‖transversePart w‖ := norm_nonneg _
  have h7 : 0 ≤ ‖perpPart d v‖ := norm_nonneg _
  nlinarith

/-- The WZ2 literal rescaling linear map. -/
def wz2LiteralLinear (d : Point3) (hd : ‖d‖ = 1) (rho : ℝ) :
    Point3 →ₗ[ℝ] Point3 :=
  (1 / 100 : ℝ) • unitRescalingLinear d hd rho

/-- Bound 1: longitudinal coordinate. -/
lemma wz2LiteralLinear_coord2
    {d : Point3} {hd : ‖d‖ = 1} {rho : ℝ} (v : Point3) :
    (wz2LiteralLinear d hd rho v) 2 = (1 / 100 : ℝ) * inner ℝ v d := by
  simp [wz2LiteralLinear, unitRescalingLinear_coord2 d hd rho v,
    PiLp.smul_apply, smul_eq_mul]

/-- Absolute value of a coordinate is bounded by the norm. -/
lemma abs_coord_le_norm (x : Point3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have hsq1 : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 :=
    point3_coord_norm_sq x
  have hsq2 : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hsq1]
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  have h9 : |x i| ^ 2 = (x i) ^ 2 := by rw [sq_abs]
  nlinarith [abs_nonneg (x i), norm_nonneg x]

/-- Bound 2: first transverse coordinate. -/
lemma wz2LiteralLinear_coord0_abs_le
    {d : Point3} {hd : ‖d‖ = 1} {rho : ℝ} {hrho : 0 < rho} (v : Point3) :
    |(wz2LiteralLinear d hd rho v) 0| ≤
      ‖perpPart d v‖ / (100 * rho) := by
  set w := householderToE3 d hd v with hw
  have hL0 : (wz2LiteralLinear d hd rho v) 0 =
      (1 / 100 : ℝ) * (w 0 / rho) := by
    simp [wz2LiteralLinear, unitRescalingLinear, transverseScaleLin_coord0,
      PiLp.smul_apply, smul_eq_mul, hw]
  rw [hL0]
  have h_abs : |(1 / 100 : ℝ) * (w 0 / rho)| =
      (1 / 100 : ℝ) * |w 0| / rho := by
    have hpos1 : (0 : ℝ) < 1 / 100 := by norm_num
    calc
      |(1 / 100 : ℝ) * (w 0 / rho)|
        = |(1 / 100 : ℝ)| * |w 0 / rho| := by rw [abs_mul]
      _ = (1 / 100 : ℝ) * |w 0 / rho| := by rw [abs_of_pos hpos1]
      _ = (1 / 100 : ℝ) * (|w 0| / |rho|) := by rw [abs_div]
      _ = (1 / 100 : ℝ) * (|w 0| / rho) := by rw [abs_of_pos hrho]
      _ = (1 / 100 : ℝ) * |w 0| / rho := by ring
  rw [h_abs]
  have h_tp0 : (transversePart w) 0 = w 0 := transversePart_coord0 w
  have h_coord_le : |w 0| ≤ ‖transversePart w‖ := by
    have h := abs_coord_le_norm (transversePart w) 0
    rw [h_tp0] at h
    exact h
  have h_norm_eq : ‖transversePart w‖ = ‖perpPart d v‖ :=
    householder_transversePart_norm_eq_perpPart hd v
  have hpos : 0 < 100 * rho := by positivity
  have h_final : |w 0| ≤ ‖perpPart d v‖ := by
    rw [h_norm_eq] at h_coord_le
    exact h_coord_le
  calc
    (1 / 100 : ℝ) * |w 0| / rho
      ≤ (1 / 100 : ℝ) * ‖perpPart d v‖ / rho := by gcongr
    _ = ‖perpPart d v‖ / (100 * rho) := by
      field_simp [hpos.ne']

/-- Bound 3: second transverse coordinate. -/
lemma wz2LiteralLinear_coord1_abs_le
    {d : Point3} {hd : ‖d‖ = 1} {rho : ℝ} {hrho : 0 < rho} (v : Point3) :
    |(wz2LiteralLinear d hd rho v) 1| ≤
      ‖perpPart d v‖ / (100 * rho) := by
  set w := householderToE3 d hd v with hw
  have hL1 : (wz2LiteralLinear d hd rho v) 1 =
      (1 / 100 : ℝ) * (w 1 / rho) := by
    simp [wz2LiteralLinear, unitRescalingLinear, transverseScaleLin_coord1,
      PiLp.smul_apply, smul_eq_mul, hw]
  rw [hL1]
  have h_abs : |(1 / 100 : ℝ) * (w 1 / rho)| =
      (1 / 100 : ℝ) * |w 1| / rho := by
    have hpos1 : (0 : ℝ) < 1 / 100 := by norm_num
    calc
      |(1 / 100 : ℝ) * (w 1 / rho)|
        = |(1 / 100 : ℝ)| * |w 1 / rho| := by rw [abs_mul]
      _ = (1 / 100 : ℝ) * |w 1 / rho| := by rw [abs_of_pos hpos1]
      _ = (1 / 100 : ℝ) * (|w 1| / |rho|) := by rw [abs_div]
      _ = (1 / 100 : ℝ) * (|w 1| / rho) := by rw [abs_of_pos hrho]
      _ = (1 / 100 : ℝ) * |w 1| / rho := by ring
  rw [h_abs]
  have h_tp1 : (transversePart w) 1 = w 1 := transversePart_coord1 w
  have h_coord_le : |w 1| ≤ ‖transversePart w‖ := by
    have h := abs_coord_le_norm (transversePart w) 1
    rw [h_tp1] at h
    exact h
  have h_norm_eq : ‖transversePart w‖ = ‖perpPart d v‖ :=
    householder_transversePart_norm_eq_perpPart hd v
  have hpos : 0 < 100 * rho := by positivity
  have h_final : |w 1| ≤ ‖perpPart d v‖ := by
    rw [h_norm_eq] at h_coord_le
    exact h_coord_le
  calc
    (1 / 100 : ℝ) * |w 1| / rho
      ≤ (1 / 100 : ℝ) * ‖perpPart d v‖ / rho := by gcongr
    _ = ‖perpPart d v‖ / (100 * rho) := by
      field_simp [hpos.ne']

/-- Bound 4: operator norm bound for `0 < rho ≤ 1`. -/
lemma wz2LiteralLinear_norm_le
    {d : Point3} {hd : ‖d‖ = 1} {rho : ℝ} {hrho : 0 < rho}
    (hrho_le_one : rho ≤ 1) (v : Point3) :
    ‖wz2LiteralLinear d hd rho v‖ ≤ ‖v‖ / (100 * rho) := by
  set w := householderToE3 d hd v with hw
  set u := transverseScaleLin rho w with hu
  have hsq : ‖u‖ ^ 2 =
      (1 / rho ^ 2) * ((w 0) ^ 2 + (w 1) ^ 2) + (w 2) ^ 2 := by
    rw [point3_coord_norm_sq u, transverseScaleLin_coord0,
      transverseScaleLin_coord1, transverseScaleLin_coord2]
    field_simp [hrho.ne']
  have h_rho2 : 1 ≤ 1 / rho ^ 2 := by
    have h2 : 0 < rho ^ 2 := by positivity
    have h3 : rho ^ 2 ≤ 1 := by nlinarith
    have h4 : 1 / rho ^ 2 ≥ 1 := by
      calc
        1 / rho ^ 2 ≥ 1 / 1 := by gcongr
        _ = 1 := by norm_num
    exact h4
  have h4 : ‖u‖ ^ 2 ≤ (1 / rho ^ 2) * ‖w‖ ^ 2 := by
    rw [hsq, point3_coord_norm_sq w]
    have h5 : (1 / rho ^ 2) * ((w 0) ^ 2 + (w 1) ^ 2) + (w 2) ^ 2 ≤
        (1 / rho ^ 2) * ((w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2) := by
      have h6 : (w 2) ^ 2 ≤ (1 / rho ^ 2) * (w 2) ^ 2 := by
        have h7 : 1 ≤ 1 / rho ^ 2 := h_rho2
        nlinarith
      nlinarith
    exact h5
  have h_norm_w : ‖w‖ = ‖v‖ := householderToE3_norm d hd v
  have h9 : (‖w‖ / rho) ^ 2 = (1 / rho ^ 2) * ‖w‖ ^ 2 := by
    field_simp [hrho.ne']
  have h10 : ‖u‖ ^ 2 ≤ (‖w‖ / rho) ^ 2 := by
    rw [h9]
    exact h4
  have h_sqrt : ‖u‖ ≤ ‖w‖ / rho := by
    have h_pos1 : 0 ≤ ‖u‖ := norm_nonneg _
    have h_pos2 : 0 ≤ ‖w‖ / rho := by positivity
    nlinarith [h10, h_pos1, h_pos2]
  have h_smul : ‖wz2LiteralLinear d hd rho v‖ =
      (1 / 100 : ℝ) * ‖u‖ := by
    have h9 : wz2LiteralLinear d hd rho v = (1 / 100 : ℝ) • u := by
      simp [wz2LiteralLinear, unitRescalingLinear, hu, hw]
    rw [h9, norm_smul]
    have h10 : ‖(1 / 100 : ℝ)‖ = (1 / 100 : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_pos] <;> norm_num
    rw [h10]
  rw [h_smul]
  calc
    (1 / 100 : ℝ) * ‖u‖
      ≤ (1 / 100 : ℝ) * (‖w‖ / rho) := by gcongr
    _ = (1 / 100 : ℝ) * (‖v‖ / rho) := by rw [h_norm_w]
    _ = ‖v‖ / (100 * rho) := by
      field_simp [hrho.ne']

end Kakeya.Assouad

end
