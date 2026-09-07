import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Re-anchoring geometry for WZ1 Property-P selection

The linear part of the coordinate change `Φ_j ∘ Φ_d⁻¹` is
`D ∘ R_j ∘ R_d ∘ D⁻¹`, where `D = transverseScaleLin (100 * rho)` and
`R_d`, `R_j` are Householder reflections.

For nearby anchors this module proves volume preservation, quantitative
horizontal and vertical distortion bounds, and a two-sided Lipschitz estimate.
These are genuinely two-anchor statements; the single-anchor API in
`UnitRescaling.lean` does not imply them directly.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-! ### Coordinate and transverse helpers -/

lemma point3_coord_norm_sq (x : Point3) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  have h1 : ‖x‖ ^ 2 = ∑ i : Fin 3, ‖x i‖ ^ 2 := EuclideanSpace.norm_sq_eq x
  have h2 : ∀ i : Fin 3, ‖x i‖ ^ 2 = (x i) ^ 2 := by
    intro i
    rw [Real.norm_eq_abs, sq_abs]
  have h4 : ∑ i : Fin 3, ‖x i‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact h2 i
  rw [h1, h4]
  simp [Fin.sum_univ_succ]
  <;> ring

lemma coord2_eq_inner_e3 (x : Point3) : x 2 = inner ℝ x e3 := by
  have h_e3 : e3 = EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    simp [e3]
  rw [h_e3]
  have h :
      inner ℝ x (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) = x 2 := by
    rw [EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ) x]
    <;> simp
  exact h.symm

lemma point3_coord0 (x y z : ℝ) : (point3 x y z) 0 = x := by
  simp [point3, PiLp.single_apply]
  <;> ring

lemma point3_coord1 (x y z : ℝ) : (point3 x y z) 1 = y := by
  simp [point3, PiLp.single_apply]
  <;> ring

lemma point3_coord2 (x y z : ℝ) : (point3 x y z) 2 = z := by
  simp [point3, PiLp.single_apply]
  <;> ring

lemma transverseScaleLin_norm_sq (rho : ℝ) (hrho : 0 < rho) (u : Point3) :
    ‖transverseScaleLin rho u‖ ^ 2 =
      (1 / rho ^ 2) * ((u 0) ^ 2 + (u 1) ^ 2) + (u 2) ^ 2 := by
  rw [point3_coord_norm_sq (transverseScaleLin rho u),
    transverseScaleLin_coord0 rho u, transverseScaleLin_coord1 rho u,
    transverseScaleLin_coord2 rho u]
  field_simp [hrho.ne']
  <;> ring

/-- If `0 < rho ≤ 1`, then `D_rho` expands norms by at most `1 / rho`. -/
lemma transverseScaleLin_norm_bound
    (rho : ℝ) (hrho : 0 < rho) (hrho_le_one : rho ≤ 1)
    (w : Point3) :
    ‖transverseScaleLin rho w‖ ≤ (1 / rho) * ‖w‖ := by
  have h1 : ‖transverseScaleLin rho w‖ ^ 2 =
      (1 / rho ^ 2) * ((w 0) ^ 2 + (w 1) ^ 2) + (w 2) ^ 2 :=
    transverseScaleLin_norm_sq rho hrho w
  have h3 : 1 / rho ^ 2 ≥ 1 := by
    have h4 : rho ^ 2 ≤ 1 := by nlinarith
    exact (one_le_div (by positivity)).mpr h4
  have h6 : (w 2) ^ 2 ≤ (1 / rho ^ 2) * (w 2) ^ 2 := by
    nlinarith [sq_nonneg (w 2)]
  have h8 :
      ‖transverseScaleLin rho w‖ ^ 2 ≤
        (1 / rho ^ 2) * ‖w‖ ^ 2 := by
    rw [h1, point3_coord_norm_sq w]
    nlinarith
  have h12 :
      ((1 / rho) * ‖w‖) ^ 2 = (1 / rho ^ 2) * ‖w‖ ^ 2 := by
    field_simp [hrho.ne']
    <;> ring
  nlinarith [norm_nonneg (transverseScaleLin rho w),
    mul_nonneg (by positivity : 0 ≤ 1 / rho) (norm_nonneg w)]

def transversePart (x : Point3) : Point3 :=
  point3 (x 0) (x 1) 0

lemma transversePart_coord0 (x : Point3) : (transversePart x) 0 = x 0 := by
  simp [transversePart, point3, PiLp.single_apply]
  <;> ring

lemma transversePart_coord1 (x : Point3) : (transversePart x) 1 = x 1 := by
  simp [transversePart, point3, PiLp.single_apply]
  <;> ring

lemma transversePart_coord2 (x : Point3) : (transversePart x) 2 = 0 := by
  simp [transversePart, point3, PiLp.single_apply]
  <;> ring

lemma transversePart_norm_sq (x : Point3) :
    ‖transversePart x‖ ^ 2 = ‖x‖ ^ 2 - (x 2) ^ 2 := by
  rw [point3_coord_norm_sq (transversePart x), point3_coord_norm_sq x]
  simp [transversePart_coord0, transversePart_coord1, transversePart_coord2]
  <;> ring

lemma transversePart_norm_scaling
    (rho : ℝ) (hrho : 0 < rho) (x : Point3) :
    ‖transversePart (transverseScaleLin rho x)‖ =
      (1 / rho) * ‖transversePart x‖ := by
  have h1 : ‖transversePart (transverseScaleLin rho x)‖ ^ 2 =
      (1 / rho ^ 2) * ((x 0) ^ 2 + (x 1) ^ 2) := by
    rw [transversePart_norm_sq, transverseScaleLin_norm_sq rho hrho,
      transverseScaleLin_coord2]
    ring
  have h5 : ‖transversePart x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    rw [transversePart_norm_sq, point3_coord_norm_sq]
    ring
  have h9 :
      ((1 / rho) * ‖transversePart x‖) ^ 2 =
        (1 / rho ^ 2) * ((x 0) ^ 2 + (x 1) ^ 2) := by
    rw [← h5]
    field_simp [hrho.ne']
    <;> ring
  nlinarith [norm_nonneg (transversePart (transverseScaleLin rho x)),
    mul_nonneg (by positivity : 0 ≤ 1 / rho) (norm_nonneg (transversePart x))]

lemma point3_decomp (y : Point3) :
    y = transversePart y + (y 2) • e3 := by
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [transversePart_coord0, transversePart_coord1,
      transversePart_coord2, e3, smul_eq_mul] <;> ring

lemma inner_transverse_left {v x : Point3} (hv : v 2 = 0) :
    inner ℝ v x = inner ℝ v (transversePart x) := by
  have h2 : x = transversePart x + (x 2) • e3 := point3_decomp x
  have h4 :
      inner ℝ v x =
        inner ℝ v (transversePart x + (x 2) • e3) := by
    exact congrArg (fun y : Point3 => inner ℝ v y) h2
  rw [h4, inner_add_right, inner_smul_right]
  have h7 : inner ℝ v e3 = v 2 := by
    rw [← coord2_eq_inner_e3 v]
  rw [h7, hv]
  ring

/-! ### Two-anchor re-anchoring map -/

def reanchoringLinear
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta) (rho : ℝ) :
    Point3 →ₗ[ℝ] Point3 :=
  (transverseScaleLin (100 * rho)).comp
    ((householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap.comp
      ((householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap.comp
        (transverseScaleLin (1 / (100 * rho)))))

/-- Re-anchoring preserves absolute determinant. -/
lemma reanchoringLinear_abs_det
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) :
    |LinearMap.det (reanchoringLinear anchor_d anchor_j rho)| = 1 := by
  let D := transverseScaleLin (100 * rho)
  let Dinv := transverseScaleLin (1 / (100 * rho))
  let R_d :=
    (householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap
  let R_j :=
    (householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap
  have hpos : 0 < 100 * rho := by positivity
  have h_det_D : LinearMap.det D = (1 / (100 * rho)) ^ 2 :=
    transverseScaleLin_det (100 * rho) hpos
  have h_det_Dinv : LinearMap.det Dinv = (100 * rho) ^ 2 := by
    have h : LinearMap.det Dinv = (1 / (1 / (100 * rho))) ^ 2 :=
      transverseScaleLin_det (1 / (100 * rho)) (by positivity)
    rw [h]
    field_simp [hpos.ne']
    <;> ring
  have h_det_Rd : |LinearMap.det R_d| = 1 :=
    householderToE3_abs_det _ _
  have h_det_Rj : |LinearMap.det R_j| = 1 :=
    householderToE3_abs_det _ _
  have h_eq :
      reanchoringLinear anchor_d anchor_j rho =
        D.comp (R_j.comp (R_d.comp Dinv)) := by
    rfl
  rw [h_eq]
  have h_main :
      LinearMap.det (D.comp (R_j.comp (R_d.comp Dinv))) =
        LinearMap.det D * LinearMap.det R_j *
          LinearMap.det R_d * LinearMap.det Dinv := by
    rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_comp]
    <;> ring
  rw [h_main]
  calc
    |LinearMap.det D * LinearMap.det R_j *
        LinearMap.det R_d * LinearMap.det Dinv| =
        |LinearMap.det D| * |LinearMap.det R_j| *
          |LinearMap.det R_d| * |LinearMap.det Dinv| := by
      simp [abs_mul]
      <;> ring
    _ = |LinearMap.det D| * |LinearMap.det Dinv| := by
      rw [h_det_Rj, h_det_Rd]
      ring
    _ = 1 := by
      rw [h_det_D, h_det_Dinv]
      rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
      field_simp [hpos.ne']
      <;> ring

/-- Swapping the two anchors gives the inverse linear map. -/
lemma reanchoringLinear_inv_eq
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) :
    (reanchoringLinear anchor_d anchor_j rho).comp
      (reanchoringLinear anchor_j anchor_d rho) = .id := by
  let D := transverseScaleLin (100 * rho)
  let Dinv := transverseScaleLin (1 / (100 * rho))
  let R_d :=
    (householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap
  let R_j :=
    (householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap
  have hDD : D.comp Dinv = .id := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [D, Dinv, transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, LinearMap.comp_apply] <;>
      field_simp [hrho.ne'] <;> ring
  have hDinvD : Dinv.comp D = .id := by
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [D, Dinv, transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, LinearMap.comp_apply] <;>
      field_simp [hrho.ne'] <;> ring
  have hRd : R_d.comp R_d = .id := by
    apply LinearMap.ext
    intro x
    exact householderToE3_involution
      anchor_d.direction anchor_d.direction_unit x
  have hRj : R_j.comp R_j = .id := by
    apply LinearMap.ext
    intro x
    exact householderToE3_involution
      anchor_j.direction anchor_j.direction_unit x
  apply LinearMap.ext
  intro x
  dsimp only [reanchoringLinear, LinearMap.comp_apply]
  have h1 :
      Dinv (D (R_d (R_j (Dinv x)))) = R_d (R_j (Dinv x)) := by
    have h := congrArg (fun L : Point3 →ₗ[ℝ] Point3 =>
      L (R_d (R_j (Dinv x)))) hDinvD
    simpa [LinearMap.comp_apply] using h
  rw [h1]
  have h2 : R_d (R_d (R_j (Dinv x))) = R_j (Dinv x) := by
    have h := congrArg (fun L : Point3 →ₗ[ℝ] Point3 =>
      L (R_j (Dinv x))) hRd
    simpa [LinearMap.comp_apply] using h
  rw [h2]
  have h3 : R_j (R_j (Dinv x)) = Dinv x := by
    have h := congrArg (fun L : Point3 →ₗ[ℝ] Point3 => L (Dinv x)) hRj
    simpa [LinearMap.comp_apply] using h
  rw [h3]
  have h4 : D (Dinv x) = x := by
    have h := congrArg (fun L : Point3 →ₗ[ℝ] Point3 => L x) hDD
    simpa [LinearMap.comp_apply] using h
  rw [h4]
  exact (LinearMap.id_apply x).symm

/-! ### Longitudinal coordinate -/

lemma reanchoringLinear_e3_z
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) :
    (reanchoringLinear anchor_d anchor_j rho e3) 2 =
      inner ℝ anchor_d.direction anchor_j.direction := by
  let D := transverseScaleLin (100 * rho)
  let Dinv := transverseScaleLin (1 / (100 * rho))
  let R_d :=
    (householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap
  let R_j :=
    (householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap
  have hDinv_e3 : Dinv e3 = e3 := by
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [Dinv, transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, e3]
  have hRd_e3 : R_d e3 = anchor_d.direction :=
    householderToE3_sends_e3_to_d _ _
  have hsymm :
      inner ℝ (R_j anchor_d.direction) e3 =
        inner ℝ anchor_d.direction (R_j e3) :=
    householderToE3_symmetric _ _ _ _
  have hRj_e3 : R_j e3 = anchor_j.direction :=
    householderToE3_sends_e3_to_d _ _
  dsimp only [reanchoringLinear, LinearMap.comp_apply]
  rw [hDinv_e3, hRd_e3, transverseScaleLin_coord2]
  rw [coord2_eq_inner_e3, hsymm, hRj_e3]

lemma reanchoringLinear_e3_z_lower
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho) :
    (reanchoringLinear anchor_d anchor_j rho e3) 2 ≥
      1 - 32 * rho ^ 2 := by
  rw [reanchoringLinear_e3_z anchor_d anchor_j rho hrho]
  have h8 :
      ‖anchor_d.direction - anchor_j.direction‖ ^ 2 =
        2 - 2 * inner ℝ anchor_d.direction anchor_j.direction := by
    rw [norm_sub_sq_real, anchor_d.direction_unit, anchor_j.direction_unit]
    ring
  have h9 :
      ‖anchor_d.direction - anchor_j.direction‖ ^ 2 ≤ (8 * rho) ^ 2 := by
    gcongr
  nlinarith

lemma transversePart_householder_bound
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho) :
    ‖transversePart
        ((householderToE3 anchor_d.direction anchor_d.direction_unit)
          anchor_j.direction)‖ ≤ 8 * rho := by
  let R_d := householderToE3 anchor_d.direction anchor_d.direction_unit
  let d := anchor_d.direction
  let j := anchor_j.direction
  set y : Point3 := R_d j
  have h1 : ‖y‖ = 1 := by
    rw [householderToE3_norm, anchor_j.direction_unit]
  have h2 : y 2 = inner ℝ d j := by
    rw [coord2_eq_inner_e3]
    rw [householderToE3_symmetric, householderToE3_sends_e3_to_d]
    exact real_inner_comm _ _
  have h3 : inner ℝ d j ≥ 1 - 32 * rho ^ 2 := by
    have h4 : ‖d - j‖ ^ 2 = 2 - 2 * inner ℝ d j := by
      rw [norm_sub_sq_real, anchor_d.direction_unit, anchor_j.direction_unit]
      ring
    have h5 : ‖d - j‖ ^ 2 ≤ (8 * rho) ^ 2 := by gcongr
    nlinarith
  have h6 : ‖transversePart y‖ ^ 2 = ‖y‖ ^ 2 - (y 2) ^ 2 :=
    transversePart_norm_sq y
  have h7 : ‖transversePart y‖ ^ 2 ≤ (8 * rho) ^ 2 := by
    rw [h6, h1, h2]
    nlinarith
  nlinarith [norm_nonneg (transversePart y)]

/-- A transverse vector acquires only `O(rho²)` longitudinal component. -/
lemma reanchoring_transverse_z_bound
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho)
    {v : Point3} (hv : v 2 = 0) :
    |(reanchoringLinear anchor_d anchor_j rho v) 2| ≤
      800 * rho ^ 2 * ‖v‖ := by
  let D := transverseScaleLin (100 * rho)
  let Dinv := transverseScaleLin (1 / (100 * rho))
  let R_d :=
    (householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap
  let R_j :=
    (householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap
  set w : Point3 := Dinv v
  have hw_eq : w = (100 * rho) • v := by
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [w, Dinv, transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, hv, smul_eq_mul] <;>
      field_simp [hrho.ne'] <;> ring
  have h1 :
      (reanchoringLinear anchor_d anchor_j rho v) 2 =
        inner ℝ w (R_d anchor_j.direction) := by
    dsimp only [reanchoringLinear, LinearMap.comp_apply]
    have h21 :
        (D (R_j (R_d w))) 2 = (R_j (R_d w)) 2 :=
      transverseScaleLin_coord2 (100 * rho) _
    rw [h21]
    have h22 :
        (R_j (R_d w)) 2 = inner ℝ (R_j (R_d w)) e3 :=
      coord2_eq_inner_e3 (R_j (R_d w))
    rw [h22]
    have h23 :
        inner ℝ (R_j (R_d w)) e3 =
          inner ℝ (R_d w) (R_j e3) :=
      householderToE3_symmetric _ _ _ _
    rw [h23]
    have h24 : R_j e3 = anchor_j.direction :=
      householderToE3_sends_e3_to_d _ _
    rw [h24]
    have h25 :
        inner ℝ (R_d w) anchor_j.direction =
          inner ℝ w (R_d anchor_j.direction) :=
      householderToE3_symmetric _ _ _ _
    rw [h25]
  rw [h1, hw_eq, inner_smul_left]
  have h4 :
      inner ℝ v (R_d anchor_j.direction) =
        inner ℝ v (transversePart (R_d anchor_j.direction)) :=
    inner_transverse_left hv
  rw [h4]
  have h5 :
      |inner ℝ v (transversePart (R_d anchor_j.direction))| ≤
        ‖v‖ * ‖transversePart (R_d anchor_j.direction)‖ :=
    abs_real_inner_le_norm v (transversePart (R_d anchor_j.direction))
  have h6 :
      ‖transversePart (R_d anchor_j.direction)‖ ≤ 8 * rho :=
    transversePart_householder_bound anchor_d anchor_j rho hrho hdir
  have hpos : 0 ≤ 100 * rho := by positivity
  calc
    |(100 * rho) * inner ℝ v (transversePart (R_d anchor_j.direction))| =
        (100 * rho) *
          |inner ℝ v (transversePart (R_d anchor_j.direction))| := by
      rw [abs_mul, abs_of_nonneg hpos]
    _ ≤ (100 * rho) *
        (‖v‖ * ‖transversePart (R_d anchor_j.direction)‖) := by
      gcongr
    _ ≤ (100 * rho) * (‖v‖ * (8 * rho)) := by
      gcongr
    _ = 800 * rho ^ 2 * ‖v‖ := by ring

/-- Re-anchoring does not expand the horizontal norm of a transverse vector. -/
lemma reanchoring_transverse_norm_upper
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho)
    {v : Point3} (hv : v 2 = 0) :
    ‖transversePart (reanchoringLinear anchor_d anchor_j rho v)‖ ≤ ‖v‖ := by
  let D := transverseScaleLin (100 * rho)
  let Dinv := transverseScaleLin (1 / (100 * rho))
  let R_d :=
    (householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap
  let R_j :=
    (householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap
  set w : Point3 := Dinv v
  set z : Point3 := R_j (R_d w)
  have h1 : reanchoringLinear anchor_d anchor_j rho v = D z := by rfl
  have h2 :
      ‖transversePart (D z)‖ =
        (1 / (100 * rho)) * ‖transversePart z‖ :=
    transversePart_norm_scaling (100 * rho) (by positivity) z
  have h3 : ‖transversePart z‖ ≤ ‖z‖ := by
    have h4 : ‖transversePart z‖ ^ 2 = ‖z‖ ^ 2 - (z 2) ^ 2 :=
      transversePart_norm_sq z
    nlinarith [sq_nonneg (z 2), norm_nonneg (transversePart z), norm_nonneg z]
  have h9 : ‖z‖ = ‖w‖ := by
    have h91 : ‖R_j (R_d w)‖ = ‖R_d w‖ :=
      householderToE3_norm _ _ _
    rw [h91]
    exact householderToE3_norm _ _ _
  have h10 : ‖w‖ = (100 * rho) * ‖v‖ := by
    have hw_eq : w = (100 * rho) • v := by
      apply PiLp.ext
      intro i
      fin_cases i <;>
        simp [w, Dinv, transverseScaleLin_coord0, transverseScaleLin_coord1,
          transverseScaleLin_coord2, hv, smul_eq_mul] <;>
        field_simp [hrho.ne'] <;> ring
    rw [hw_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h1, h2]
  have h11 :
      (1 / (100 * rho)) * ‖transversePart z‖ ≤
        (1 / (100 * rho)) * ‖z‖ := by
    gcongr
  rw [h9, h10] at h11
  have h12 :
      (1 / (100 * rho)) * ((100 * rho) * ‖v‖) = ‖v‖ := by
    field_simp [hrho.ne']
    <;> ring
  rwa [h12] at h11

/--
For transverse `v`, the horizontal norm loses at most the factor
`1 - 64 * rho²`.
-/
lemma reanchoring_transverse_norm_lower
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho)
    {v : Point3} (hv : v 2 = 0) :
    ‖transversePart (reanchoringLinear anchor_d anchor_j rho v)‖ ≥
      (1 - 64 * rho ^ 2) * ‖v‖ := by
  let D := transverseScaleLin (100 * rho)
  let Dinv := transverseScaleLin (1 / (100 * rho))
  let R_d :=
    (householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap
  let R_j :=
    (householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap
  set w : Point3 := Dinv v
  set z : Point3 := R_j (R_d w)
  have h1 : reanchoringLinear anchor_d anchor_j rho v = D z := by rfl
  have h2 :
      ‖transversePart (D z)‖ =
        (1 / (100 * rho)) * ‖transversePart z‖ :=
    transversePart_norm_scaling (100 * rho) (by positivity) z
  have h3 : ‖transversePart z‖ ^ 2 = ‖z‖ ^ 2 - (z 2) ^ 2 :=
    transversePart_norm_sq z
  have h4 : ‖z‖ = (100 * rho) * ‖v‖ := by
    have h41 : ‖R_j (R_d w)‖ = ‖R_d w‖ :=
      householderToE3_norm _ _ _
    rw [h41]
    have h42 : ‖R_d w‖ = ‖w‖ :=
      householderToE3_norm _ _ _
    rw [h42]
    have hw_eq : w = (100 * rho) • v := by
      apply PiLp.ext
      intro i
      fin_cases i <;>
        simp [w, Dinv, transverseScaleLin_coord0, transverseScaleLin_coord1,
          transverseScaleLin_coord2, hv, smul_eq_mul] <;>
        field_simp [hrho.ne'] <;> ring
    rw [hw_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h5 : |z 2| ≤ 800 * rho ^ 2 * ‖v‖ := by
    have h51 : z 2 = (reanchoringLinear anchor_d anchor_j rho v) 2 := by
      dsimp only [z, reanchoringLinear, LinearMap.comp_apply]
      rw [transverseScaleLin_coord2]
    rw [h51]
    exact reanchoring_transverse_z_bound
      anchor_d anchor_j rho hrho hrho_small hdir hv
  have h6 : (z 2) ^ 2 ≤ (800 * rho ^ 2 * ‖v‖) ^ 2 := by
    rw [show (z 2) ^ 2 = |z 2| ^ 2 by rw [sq_abs]]
    gcongr
  have h9 :
      ‖transversePart z‖ ^ 2 ≥
        ((100 * rho) * ‖v‖) ^ 2 -
          (800 * rho ^ 2 * ‖v‖) ^ 2 := by
    rw [h3, h4]
    nlinarith
  have h11 : 0 ≤ 1 - 64 * rho ^ 2 := by
    nlinarith
  have h13 :
      ((100 * rho) * ‖v‖) ^ 2 -
          (800 * rho ^ 2 * ‖v‖) ^ 2 =
        ((100 * rho) * ‖v‖) ^ 2 * (1 - 64 * rho ^ 2) := by
    ring
  rw [h13] at h9
  have h14 :
      ‖transversePart z‖ ≥
        (100 * rho) * ‖v‖ * Real.sqrt (1 - 64 * rho ^ 2) := by
    nlinarith [norm_nonneg (transversePart z),
      Real.sqrt_nonneg (1 - 64 * rho ^ 2), Real.sq_sqrt h11]
  have h17 : Real.sqrt (1 - 64 * rho ^ 2) ≥ 1 - 64 * rho ^ 2 := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  rw [h1, h2]
  have h20 :
      (1 / (100 * rho)) * ‖transversePart z‖ ≥
        (1 / (100 * rho)) *
          ((100 * rho) * ‖v‖ * Real.sqrt (1 - 64 * rho ^ 2)) := by
    gcongr
  have h21 :
      (1 / (100 * rho)) *
          ((100 * rho) * ‖v‖ * Real.sqrt (1 - 64 * rho ^ 2)) =
        ‖v‖ * Real.sqrt (1 - 64 * rho ^ 2) := by
    field_simp [hrho.ne']
    <;> ring
  rw [h21] at h20
  have h22 :
      ‖v‖ * Real.sqrt (1 - 64 * rho ^ 2) ≥
        ‖v‖ * (1 - 64 * rho ^ 2) := by
    gcongr
  linarith

/-- The image of the longitudinal unit vector has norm at most `11 / 10`. -/
lemma reanchoring_e3_norm_bound
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho) :
    ‖reanchoringLinear anchor_d anchor_j rho e3‖ ≤ 11 / 10 := by
  let D := transverseScaleLin (100 * rho)
  let Dinv := transverseScaleLin (1 / (100 * rho))
  let R_d :=
    (householderToE3 anchor_d.direction anchor_d.direction_unit).toLinearMap
  let R_j :=
    (householderToE3 anchor_j.direction anchor_j.direction_unit).toLinearMap
  have hDinv_e3 : Dinv e3 = e3 := by
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [Dinv, transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, e3]
  have hRd_e3 : R_d e3 = anchor_d.direction :=
    householderToE3_sends_e3_to_d _ _
  set z : Point3 := R_j anchor_d.direction
  have h1 : reanchoringLinear anchor_d anchor_j rho e3 = D z := by
    dsimp only [reanchoringLinear, LinearMap.comp_apply]
    rw [hDinv_e3, hRd_e3]
  have hdir' : ‖anchor_j.direction - anchor_d.direction‖ ≤ 8 * rho := by
    simpa [norm_sub_rev] using hdir
  have h3 : ‖transversePart z‖ ≤ 8 * rho :=
    transversePart_householder_bound anchor_j anchor_d rho hrho hdir'
  have h4 : (z 0) ^ 2 + (z 1) ^ 2 = ‖transversePart z‖ ^ 2 := by
    rw [transversePart_norm_sq, point3_coord_norm_sq]
    ring
  have h6 : ‖transversePart z‖ ^ 2 ≤ (8 * rho) ^ 2 := by gcongr
  have h8 : ‖z‖ = 1 := by
    have h81 : ‖z‖ = ‖anchor_d.direction‖ :=
      householderToE3_norm
        anchor_j.direction anchor_j.direction_unit anchor_d.direction
    rw [h81, anchor_d.direction_unit]
  have h7 : (z 2) ^ 2 ≤ 1 := by
    have h9 : (z 2) ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [point3_coord_norm_sq]
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    rw [h8] at h9
    nlinarith
  have h2 :
      ‖D z‖ ^ 2 =
        (1 / (100 * rho) ^ 2) * ((z 0) ^ 2 + (z 1) ^ 2) + (z 2) ^ 2 :=
    transverseScaleLin_norm_sq (100 * rho) (by positivity) z
  have h101 :
      (1 / (100 * rho) ^ 2) * ((z 0) ^ 2 + (z 1) ^ 2) ≤
        (1 / (100 * rho) ^ 2) * (8 * rho) ^ 2 := by
    gcongr
    linarith
  have h102 :
      (1 / (100 * rho) ^ 2) * (8 * rho) ^ 2 = 64 / 10000 := by
    field_simp [hrho.ne']
    <;> ring
  have h103 : ‖D z‖ ^ 2 ≤ 64 / 10000 + 1 := by
    calc
      ‖D z‖ ^ 2 =
          (1 / (100 * rho) ^ 2) * ((z 0) ^ 2 + (z 1) ^ 2) +
            (z 2) ^ 2 := h2
      _ ≤ (1 / (100 * rho) ^ 2) * (8 * rho) ^ 2 + 1 := by
        gcongr
      _ = 64 / 10000 + 1 := by rw [h102]
  have h10 : ‖D z‖ ^ 2 ≤ (11 / 10 : ℝ) ^ 2 := by
    have h104 : (64 / 10000 + 1 : ℝ) ≤ (11 / 10 : ℝ) ^ 2 := by
      norm_num
    exact h103.trans h104
  rw [h1]
  nlinarith [norm_nonneg (D z)]

/-! ### Full two-sided norm bounds -/

lemma reanchoringLinear_norm_bound
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho)
    (v : Point3) :
    ‖reanchoringLinear anchor_d anchor_j rho v‖ ≤ 2 * ‖v‖ := by
  let S := reanchoringLinear anchor_d anchor_j rho
  set vT : Point3 := transversePart v
  set vZ : Point3 := v - vT
  have hvT2 : vT 2 = 0 := transversePart_coord2 v
  have hvZ_eq : vZ = (v 2) • e3 := by
    apply PiLp.ext
    intro i
    fin_cases i <;>
      simp [vZ, vT, transversePart_coord0, transversePart_coord1,
        transversePart_coord2, e3, smul_eq_mul] <;> ring
  have h_vadd : v = vT + vZ := by
    simp [vZ, vT]
    <;> abel
  have h1 : S v = S vT + S vZ := by
    rw [h_vadd, map_add]
  have h_bound_vT : ‖S vT‖ ≤ (11 / 10 : ℝ) * ‖vT‖ := by
    set w : Point3 := S vT
    have h_decomp : w = transversePart w + (w 2) • e3 := point3_decomp w
    have h21 : ‖w‖ ≤ ‖transversePart w‖ + |w 2| := by
      have h_eq :
          ‖w‖ = ‖transversePart w + (w 2) • e3‖ :=
        congrArg (fun x : Point3 => ‖x‖) h_decomp
      rw [h_eq]
      have h3 :
          ‖transversePart w + (w 2) • e3‖ ≤
            ‖transversePart w‖ + ‖(w 2) • e3‖ :=
        norm_add_le _ _
      have h4 : ‖(w 2) • e3‖ = |w 2| := by
        rw [norm_smul, e3_norm]
        simp [Real.norm_eq_abs]
      rw [h4] at h3
      exact h3
    have h22 : ‖transversePart w‖ ≤ ‖vT‖ :=
      reanchoring_transverse_norm_upper
        anchor_d anchor_j rho hrho hrho_small hdir hvT2
    have h23 : |w 2| ≤ 800 * rho ^ 2 * ‖vT‖ :=
      reanchoring_transverse_z_bound
        anchor_d anchor_j rho hrho hrho_small hdir hvT2
    have h24 : 800 * rho ^ 2 ≤ 1 / 10 := by
      have h26 : rho ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by gcongr
      nlinarith
    calc
      ‖S vT‖ = ‖w‖ := rfl
      _ ≤ ‖transversePart w‖ + |w 2| := h21
      _ ≤ ‖vT‖ + 800 * rho ^ 2 * ‖vT‖ := by
        gcongr
      _ ≤ (11 / 10 : ℝ) * ‖vT‖ := by
        nlinarith [norm_nonneg vT]
  have h_bound_vZ : ‖S vZ‖ ≤ (11 / 10 : ℝ) * ‖vZ‖ := by
    have h31 : S vZ = (v 2) • S e3 := by
      rw [hvZ_eq, map_smul]
    rw [h31, norm_smul]
    have h32 : ‖S e3‖ ≤ 11 / 10 :=
      reanchoring_e3_norm_bound
        anchor_d anchor_j rho hrho hrho_small hdir
    have h34 : ‖vZ‖ = ‖(v 2 : ℝ)‖ := by
      rw [hvZ_eq, norm_smul, e3_norm]
      ring
    rw [h34]
    calc
      ‖(v 2 : ℝ)‖ * ‖S e3‖ ≤
          ‖(v 2 : ℝ)‖ * (11 / 10 : ℝ) := by
        gcongr
      _ = (11 / 10 : ℝ) * ‖(v 2 : ℝ)‖ := by ring
  have h4 : ‖S vT + S vZ‖ ≤ ‖S vT‖ + ‖S vZ‖ := norm_add_le _ _
  have h5 :
      ‖S vT‖ + ‖S vZ‖ ≤
        (11 / 10 : ℝ) * (‖vT‖ + ‖vZ‖) := by
    linarith
  have h6 :
      (‖vT‖ + ‖vZ‖) ^ 2 ≤ 2 * (‖vT‖ ^ 2 + ‖vZ‖ ^ 2) := by
    nlinarith [sq_nonneg (‖vT‖ - ‖vZ‖)]
  have h7 : ‖vT‖ ^ 2 + ‖vZ‖ ^ 2 = ‖v‖ ^ 2 := by
    have h71 : ‖vZ‖ ^ 2 = (v 2) ^ 2 := by
      rw [hvZ_eq, norm_smul, e3_norm]
      simp [Real.norm_eq_abs, sq_abs]
      <;> ring
    have h72 : ‖vT‖ ^ 2 = ‖v‖ ^ 2 - (v 2) ^ 2 :=
      transversePart_norm_sq v
    linarith
  have h9 : ‖vT‖ + ‖vZ‖ ≤ Real.sqrt 2 * ‖v‖ := by
    have h10 : (‖vT‖ + ‖vZ‖) ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
      rw [h7] at h6
      exact h6
    have h11 : 0 ≤ Real.sqrt 2 * ‖v‖ := by positivity
    nlinarith [Real.sqrt_nonneg 2,
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      norm_nonneg vT, norm_nonneg vZ, norm_nonneg v, h11]
  calc
    ‖S v‖ = ‖S vT + S vZ‖ := by rw [h1]
    _ ≤ (11 / 10 : ℝ) * (‖vT‖ + ‖vZ‖) := h4.trans h5
    _ ≤ (11 / 10 : ℝ) * (Real.sqrt 2 * ‖v‖) := by gcongr
    _ ≤ 2 * ‖v‖ := by
      have h12 : (11 / 10 : ℝ) * Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sqrt_nonneg 2,
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      nlinarith [norm_nonneg v]

lemma reanchoringLinear_inv_norm_bound
    {delta : ℝ} (anchor_d anchor_j : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho)
    (v : Point3) :
    ‖reanchoringLinear anchor_j anchor_d rho v‖ ≤ 2 * ‖v‖ := by
  have hdir' : ‖anchor_j.direction - anchor_d.direction‖ ≤ 8 * rho := by
    simpa [norm_sub_rev] using hdir
  exact reanchoringLinear_norm_bound
    anchor_j anchor_d rho hrho hrho_small hdir' v

/-- The re-anchoring map is `2`-Lipschitz. -/
lemma reanchoring_tube_enclosure
    {delta : ℝ} {anchor_d anchor_j : Kakeya.DeltaTube delta}
    {rho : ℝ} {hrho : 0 < rho} {hrho_small : rho ≤ 1 / 100}
    {hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho}
    {x y : Point3} :
    dist (reanchoringLinear anchor_d anchor_j rho x)
        (reanchoringLinear anchor_d anchor_j rho y) ≤
      2 * dist x y := by
  let S := reanchoringLinear anchor_d anchor_j rho
  have h : dist (S x) (S y) = ‖S (x - y)‖ := by
    simp [dist_eq_norm, map_sub]
  rw [h]
  have h2 : ‖S (x - y)‖ ≤ 2 * ‖x - y‖ :=
    reanchoringLinear_norm_bound
      anchor_d anchor_j rho hrho hrho_small hdir (x - y)
  simpa [dist_eq_norm] using h2

/-- The inverse bound gives the other half of the bi-Lipschitz estimate. -/
lemma reanchoring_point_dist_lower
    {delta : ℝ} {anchor_d anchor_j : Kakeya.DeltaTube delta}
    {rho : ℝ} {hrho : 0 < rho} {hrho_small : rho ≤ 1 / 100}
    {hdir : ‖anchor_d.direction - anchor_j.direction‖ ≤ 8 * rho}
    {a b : Point3} :
    dist a b ≤
      2 * dist (reanchoringLinear anchor_d anchor_j rho a)
        (reanchoringLinear anchor_d anchor_j rho b) := by
  have h_inv :
      (reanchoringLinear anchor_j anchor_d rho).comp
          (reanchoringLinear anchor_d anchor_j rho) = .id :=
    reanchoringLinear_inv_eq anchor_j anchor_d rho hrho
  have h2 :
      reanchoringLinear anchor_j anchor_d rho
          (reanchoringLinear anchor_d anchor_j rho a) = a := by
    have h := congrArg (fun L : Point3 →ₗ[ℝ] Point3 => L a) h_inv
    simpa [LinearMap.comp_apply] using h
  have h3 :
      reanchoringLinear anchor_j anchor_d rho
          (reanchoringLinear anchor_d anchor_j rho b) = b := by
    have h := congrArg (fun L : Point3 →ₗ[ℝ] Point3 => L b) h_inv
    simpa [LinearMap.comp_apply] using h
  have hdir' : ‖anchor_j.direction - anchor_d.direction‖ ≤ 8 * rho := by
    simpa [norm_sub_rev] using hdir
  have h4 :=
    reanchoring_tube_enclosure
      (anchor_d := anchor_j) (anchor_j := anchor_d)
      (hrho := hrho) (hrho_small := hrho_small) (hdir := hdir')
      (x := reanchoringLinear anchor_d anchor_j rho a)
      (y := reanchoringLinear anchor_d anchor_j rho b)
  rwa [h2, h3] at h4

/-! ### Single-anchor image control -/

/-- The single-anchor linear part expands by at most `1 / (100 * rho)`. -/
lemma anchoredRescalingLinear_norm_bound
    {delta : ℝ} (anchor : Kakeya.DeltaTube delta)
    (rho : ℝ) (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (v : Point3) :
    ‖(transverseScaleLin (100 * rho)).comp
      ((householderToE3 anchor.direction anchor.direction_unit).toLinearMap) v‖ ≤
      (1 / (100 * rho)) * ‖v‖ := by
  let R :=
    (householderToE3 anchor.direction anchor.direction_unit).toLinearMap
  let D := transverseScaleLin (100 * rho)
  have h1 : ‖R v‖ = ‖v‖ := householderToE3_norm _ _ _
  have h2 : ‖D (R v)‖ ≤ (1 / (100 * rho)) * ‖R v‖ :=
    transverseScaleLin_norm_bound
      (100 * rho) (by positivity) (by linarith) (R v)
  rwa [h1] at h2

/--
The image of a subset of a `delta`-tube lies in the `delta / rho`
thickening of the image of its unit segment.
-/
lemma source_image_subset
    {delta rho : ℝ} (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 100)
    (anchor : Kakeya.DeltaTube delta) (T : Kakeya.DeltaTube delta)
    (X : Set Point3) (hX : X ⊆ T.carrier) :
    wz1AnchoredUnitRescalingMap anchor rho hrho '' X ⊆
      Metric.cthickening (delta / rho)
        (wz1AnchoredUnitRescalingMap anchor rho hrho ''
          unitSegment T.base T.direction) := by
  let Φ := wz1AnchoredUnitRescalingMap anchor rho hrho
  let L := (transverseScaleLin (100 * rho)).comp
    ((householderToE3 anchor.direction anchor.direction_unit).toLinearMap
      )
  let S := unitSegment T.base T.direction
  have hL_bound : ∀ v : Point3, ‖L v‖ ≤ (1 / (100 * rho)) * ‖v‖ :=
    anchoredRescalingLinear_norm_bound anchor rho hrho hrho_small
  have h_affine : ∀ p q : Point3, Φ p - Φ q = L (p - q) := by
    intro p q
    exact wz1AnchoredUnitRescalingMap_sub anchor rho hrho p q
  have h_compact : IsCompact S := by
    apply IsCompact.image isCompact_Icc
    exact continuous_const.add (continuous_id.smul continuous_const)
  have h_nonempty : S.Nonempty := by
    exact ⟨T.base, ⟨0, by norm_num, by simp⟩⟩
  intro y hy
  rcases hy with ⟨p, hpX, rfl⟩
  have hpT : p ∈ T.carrier := hX hpX
  have h_dist1 : infEDist p S ≤ ENNReal.ofReal delta := by
    exact (Metric.mem_cthickening_iff.mp (by simpa [DeltaTube.carrier] using hpT))
  by_cases hdelta : 0 ≤ delta
  · obtain ⟨q, hq, hq2⟩ :=
      h_compact.exists_infEDist_eq_edist h_nonempty p
    have h3 : edist p q ≤ ENNReal.ofReal delta := by
      rw [← hq2]
      exact h_dist1
    have h4 : dist p q ≤ delta := by
      rwa [edist_le_ofReal hdelta] at h3
    have h_image_q : Φ q ∈ Φ '' S := ⟨q, hq, rfl⟩
    have h_main : dist (Φ p) (Φ q) ≤ delta / rho := by
      rw [show dist (Φ p) (Φ q) = ‖Φ p - Φ q‖ by rfl, h_affine]
      have h3' : ‖L (p - q)‖ ≤ (1 / (100 * rho)) * ‖p - q‖ :=
        hL_bound (p - q)
      have h5 :
          (1 / (100 * rho)) * dist p q ≤
            (1 / (100 * rho)) * delta := by
        gcongr
      have h6 : (1 / (100 * rho)) * delta ≤ delta / rho := by
        field_simp [hrho.ne']
        nlinarith
      simpa [dist_eq_norm] using h3'.trans (h5.trans h6)
    exact Metric.mem_cthickening_of_dist_le
      (Φ p) (Φ q) (delta / rho) (Φ '' S) h_image_q h_main
  · have hdelta_neg : delta < 0 := by linarith
    have h2 : ENNReal.ofReal delta = 0 :=
      ENNReal.ofReal_eq_zero.mpr hdelta_neg.le
    rw [h2] at h_dist1
    have h3 : infEDist p S = 0 := le_zero_iff.mp h_dist1
    have h4 : p ∈ closure S := by
      rwa [Metric.mem_closure_iff_infEDist_zero]
    have h6 : p ∈ S := by
      simpa [h_compact.isClosed.closure_eq] using h4
    have h7 : Φ p ∈ Φ '' S := ⟨p, h6, rfl⟩
    have h8 : infEDist (Φ p) (Φ '' S) = 0 :=
      Metric.infEDist_zero_of_mem h7
    have h9 :
        infEDist (Φ p) (Φ '' S) ≤ ENNReal.ofReal (delta / rho) := by
      rw [h8]
      simp
    exact Metric.mem_cthickening_iff.mpr h9

end Kakeya.Assouad
