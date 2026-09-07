import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetShearNormal

/-!
# Projective normalization of offset-shear normals

This is deliberately just the elementary chart calculation.  It does not
choose the chart or assert any geometric lower bound for it.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Normalize an offset-shear normal in the chart where coordinate `1` is one. -/
def pureWZ2OffsetShearProjectiveNormal (a : ℝ) (normal : Point3) : Point3 :=
  (pureWZ2OffsetShearNormal a normal 1)⁻¹ • pureWZ2OffsetShearNormal a normal

@[simp] theorem pureWZ2OffsetShearProjectiveNormal_coord_one
    {a : ℝ} {normal : Point3}
    (hnonzero : pureWZ2OffsetShearNormal a normal 1 ≠ 0) :
    pureWZ2OffsetShearProjectiveNormal a normal 1 = 1 := by
  simp only [pureWZ2OffsetShearProjectiveNormal, PiLp.smul_apply]
  exact inv_mul_cancel₀ hnonzero

private lemma pureWZ2_abs_coord_le_norm (vector : Point3) (coordinate : Fin 3) :
    |vector coordinate| ≤ ‖vector‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le vector coordinate

/-- A bounded raw normal with chart coordinate bounded below has bounded
projective representative. -/
theorem norm_pureWZ2OffsetShearProjectiveNormal_le
    {a B c : ℝ} {normal : Point3}
    (hc : 0 < c)
    (hnorm : ‖pureWZ2OffsetShearNormal a normal‖ ≤ B)
    (hcoord : c ≤ |pureWZ2OffsetShearNormal a normal 1|) :
    ‖pureWZ2OffsetShearProjectiveNormal a normal‖ ≤ B / c := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hnorm
  rw [pureWZ2OffsetShearProjectiveNormal, norm_smul, Real.norm_eq_abs]
  rw [abs_inv]
  calc
    |pureWZ2OffsetShearNormal a normal 1|⁻¹ * ‖pureWZ2OffsetShearNormal a normal‖ ≤
        |pureWZ2OffsetShearNormal a normal 1|⁻¹ * B := by
      gcongr
    _ ≤ c⁻¹ * B := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [one_div] using one_div_le_one_div_of_le hc hcoord)
        hB
    _ = B / c := by ring

/-- The projective chart is Lipschitz on bounded normals whose chart
coordinates have absolute value at least `c`.  The constant is intentionally
the safe `1/c + B/c^2`. -/
theorem pureWZ2OffsetShearProjectiveNormal_sub_le
    {a B c : ℝ} {first second : Point3}
    (hc : 0 < c)
    (hsecond_norm : ‖pureWZ2OffsetShearNormal a second‖ ≤ B)
    (hfirst_coord : c ≤ |pureWZ2OffsetShearNormal a first 1|)
    (hsecond_coord : c ≤ |pureWZ2OffsetShearNormal a second 1|) :
    ‖pureWZ2OffsetShearProjectiveNormal a first -
        pureWZ2OffsetShearProjectiveNormal a second‖ ≤
      (1 / c + B / c ^ 2) *
        ‖pureWZ2OffsetShearNormal a first - pureWZ2OffsetShearNormal a second‖ := by
  let u := pureWZ2OffsetShearNormal a first 1
  let v := pureWZ2OffsetShearNormal a second 1
  let x := pureWZ2OffsetShearNormal a first
  let y := pureWZ2OffsetShearNormal a second
  have hu : c ≤ |u| := hfirst_coord
  have hv : c ≤ |v| := hsecond_coord
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, abs_zero] at hu
    linarith
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hv
    linarith
  have hcoord : |u - v| ≤ ‖x - y‖ := by
    have h := pureWZ2_abs_coord_le_norm (x - y) (1 : Fin 3)
    simpa [u, v, x, y] using h
  have hcoord' : |v - u| ≤ ‖x - y‖ := by
    simpa only [abs_sub_comm] using hcoord
  have hinv : |u⁻¹ - v⁻¹| ≤ (1 / c ^ 2) * ‖x - y‖ := by
    rw [inv_sub_inv hu0 hv0, abs_div, abs_mul]
    have hdenom : c ^ 2 ≤ |u| * |v| := by
      simpa [pow_two] using mul_le_mul hu hv hc.le (abs_nonneg u)
    have hquot : |v - u| / (|u| * |v|) ≤ |v - u| / c ^ 2 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hc) hdenom
    calc
      |v - u| / (|u| * |v|) ≤ |v - u| / c ^ 2 := hquot
      _ ≤ ‖x - y‖ / c ^ 2 := (div_le_div_iff_of_pos_right (sq_pos_of_pos hc)).mpr hcoord'
      _ = (1 / c ^ 2) * ‖x - y‖ := by ring
  have hinv_bound : |u⁻¹| ≤ 1 / c := by
    rw [abs_inv]
    simpa [one_div] using one_div_le_one_div_of_le hc hu
  have hdecomp : u⁻¹ • x - v⁻¹ • y =
      u⁻¹ • (x - y) + (u⁻¹ - v⁻¹) • y := by
    rw [smul_sub, sub_smul]
    abel
  rw [pureWZ2OffsetShearProjectiveNormal]
  change ‖u⁻¹ • x - v⁻¹ • y‖ ≤ (1 / c + B / c ^ 2) * ‖x - y‖
  rw [hdecomp]
  calc
    ‖u⁻¹ • (x - y) + (u⁻¹ - v⁻¹) • y‖ ≤
        ‖u⁻¹ • (x - y)‖ + ‖(u⁻¹ - v⁻¹) • y‖ := norm_add_le _ _
    _ = |u⁻¹| * ‖x - y‖ + |u⁻¹ - v⁻¹| * ‖y‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (1 / c) * ‖x - y‖ + ((1 / c ^ 2) * ‖x - y‖) * B := by
      gcongr
    _ = (1 / c + B / c ^ 2) * ‖x - y‖ := by ring

/-- A raw normal map which is Lipschitz, bounded, and remains in this
chart induces a Lipschitz projective normal map. -/
theorem pureWZ2OffsetShearProjectiveNormal_lipschitz
    {X : Type*} [PseudoMetricSpace X] {a : ℝ} {B c K : NNReal}
    {rawNormal : X → Point3}
    (hraw : LipschitzWith K (fun point => pureWZ2OffsetShearNormal a (rawNormal point)))
    (hc : 0 < (c : ℝ))
    (hnorm : ∀ point, ‖pureWZ2OffsetShearNormal a (rawNormal point)‖ ≤ B)
    (hcoord : ∀ point, (c : ℝ) ≤ |pureWZ2OffsetShearNormal a (rawNormal point) 1|) :
    LipschitzWith ((c⁻¹ + B * c⁻¹ ^ 2) * K)
      (fun point => pureWZ2OffsetShearProjectiveNormal a (rawNormal point)) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hprojective := pureWZ2OffsetShearProjectiveNormal_sub_le hc
    (hnorm second) (hcoord first) (hcoord second)
  have hraw_bound := hraw.dist_le_mul first second
  change ‖pureWZ2OffsetShearProjectiveNormal a (rawNormal first) -
      pureWZ2OffsetShearProjectiveNormal a (rawNormal second)‖ ≤
    (((c⁻¹ + B * c⁻¹ ^ 2) * K : NNReal) : ℝ) * dist first second
  calc
    ‖pureWZ2OffsetShearProjectiveNormal a (rawNormal first) -
        pureWZ2OffsetShearProjectiveNormal a (rawNormal second)‖ ≤
        (1 / (c : ℝ) + (B : ℝ) / (c : ℝ) ^ 2) *
          ‖pureWZ2OffsetShearNormal a (rawNormal first) -
            pureWZ2OffsetShearNormal a (rawNormal second)‖ := hprojective
    _ ≤ (1 / (c : ℝ) + (B : ℝ) / (c : ℝ) ^ 2) *
          ((K : ℝ) * dist first second) := by
      gcongr
      simpa only [dist_eq_norm] using hraw_bound
    _ = (((c⁻¹ + B * c⁻¹ ^ 2) * K : NNReal) : ℝ) *
          dist first second := by
      norm_num [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_inv]
      ring

/-- Projectivize the genuine Node-5 plane map in the half-offset shear chart.
The hypotheses are exactly the internal compatibility certificate together
with a short-window bound for the global slope. -/
theorem
    PureWZ2LocalGlobalCompatibility.offsetShearProjectiveNormal_lipschitz
    {sigma loss delta anchorSlope : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (hanchor : |anchorSlope| ≤ 1)
    (hclose : ∀ point : {point : Point3 // point ∈ cfg.shading.union},
      |cfg.globalGrains.slope (point.1 2) - anchorSlope| ≤ 1 / 200) :
    LipschitzWith 10100
      (fun point => pureWZ2OffsetShearProjectiveNormal
        (pureWZ2HalfOffset anchorSlope)
        (cfg.localGrains.planeMap point)) := by
  let a := pureWZ2HalfOffset anchorSlope
  have ha : |a| ≤ 1 / 2 := pureWZ2HalfOffset_abs_le hanchor
  have hraw : LipschitzWith 2
      (fun point => pureWZ2OffsetShearNormal a
        (cfg.localGrains.planeMap point)) := by
    simpa using pureWZ2OffsetShearNormal_lipschitz ha
      cfg.localGrains.planeMap_lipschitz
  have hnorm : ∀ point,
      ‖pureWZ2OffsetShearNormal a
        (cfg.localGrains.planeMap point)‖ ≤ 2 := by
    intro point
    simpa [cfg.localGrains.planeMap_unit point] using
      pureWZ2OffsetShearNormal_norm_le_two ha
        (cfg.localGrains.planeMap point)
  have hcoord : ∀ point,
      ((1 / 50 : ℝ) : ℝ) ≤
        |pureWZ2OffsetShearNormal a
          (cfg.localGrains.planeMap point) 1| := by
    intro point
    exact (compatibility.offsetShearNormal_coord_one_lower point
      (hclose point)).le
  have hlip := pureWZ2OffsetShearProjectiveNormal_lipschitz
    (a := a) (B := (2 : NNReal)) (c := (1 / 50 : NNReal))
    (K := (2 : NNReal)) hraw (by norm_num) hnorm hcoord
  have hconstant : (((1 / 50 : NNReal)⁻¹ +
      (2 : NNReal) * (1 / 50 : NNReal)⁻¹ ^ 2) * 2) = 10100 := by
    norm_num
  rw [← hconstant]
  exact hlip

/-- In the same chart, the projective representative has second coordinate
exactly one at every point. -/
theorem PureWZ2LocalGlobalCompatibility.offsetShearProjectiveNormal_coord_one
    {sigma loss delta anchorSlope : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (hclose : ∀ point : {point : Point3 // point ∈ cfg.shading.union},
      |cfg.globalGrains.slope (point.1 2) - anchorSlope| ≤ 1 / 200)
    (point : {point : Point3 // point ∈ cfg.shading.union}) :
    pureWZ2OffsetShearProjectiveNormal (pureWZ2HalfOffset anchorSlope)
        (cfg.localGrains.planeMap point) 1 = 1 := by
  apply pureWZ2OffsetShearProjectiveNormal_coord_one
  have hpositive := compatibility.offsetShearNormal_coord_one_lower point
    (hclose point)
  intro hzero
  rw [hzero, abs_zero] at hpositive
  norm_num at hpositive

end Kakeya.Assouad

end
