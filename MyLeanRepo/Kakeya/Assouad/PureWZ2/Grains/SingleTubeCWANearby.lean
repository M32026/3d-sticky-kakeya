import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization.Basic
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import Mathlib.Tactic

/-!
# Single-tube nearby-scales CWA via self-cover (Strategy 1, outputLoss ≥ 2)

## Geometric core

A ρ-tube (ρ ≤ 1) is contained in an explicit ellipsoid with semi-axes
`a = ρ+1/2`, `b = √(ρa)`, determinant `ρa² ≤ 9/4`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set MeasureTheory Classical

attribute [local instance] Classical.propDecidable

/-- Key algebraic inequality for ellipsoid containment.

Given `u² + r² ≤ ρ²` and `t ∈ [0,1]`, the point with axial offset `t-1/2+u`
and perpendicular squared-radius `r²` lies inside the ellipsoid with
semi-axes `a = ρ+1/2` and `b² = ρa`. -/
private lemma ellipsoid_algebraic_ineq
    (rho t u r2 : ℝ) (hrho : 0 < rho)
    (ht1 : 0 ≤ t) (ht2 : t ≤ 1)
    (h : u^2 + r2 ≤ rho^2) :
    (t - 1 / 2 + u)^2 / (rho + 1 / 2)^2 + r2 / (rho * (rho + 1 / 2)) ≤ 1 := by
  set a : ℝ := rho + 1 / 2 with ha
  set b2 : ℝ := rho * a with hb2
  have ha_pos : 0 < a := by positivity
  have hb2_pos : 0 < b2 := by positivity
  set c : ℝ := t - 1 / 2 with hc
  have hc2 : c^2 ≤ 1 / 4 := by
    rw [hc] <;> nlinarith
  have h_r2_le : r2 ≤ rho^2 - u^2 := by nlinarith
  have h_pos1 : 0 < a^2 * b2 := by positivity
  have h_main : b2 * (c + u)^2 + a^2 * r2 ≤ a^2 * b2 := by
    have h1 : b2 * (c + u)^2 + a^2 * r2 ≤ b2 * (c + u)^2 + a^2 * (rho^2 - u^2) := by
      gcongr
      <;> nlinarith
    have h2 : b2 * (c + u)^2 + a^2 * (rho^2 - u^2) ≤ a^2 * b2 := by
      have hq : 4 * rho * c * u - u^2 ≤ 4 * rho^2 * c^2 := by
        have hsq : 0 ≤ (u - 2 * rho * c)^2 := by positivity
        nlinarith
      have h3 : 2 * rho * c^2 + 4 * rho * c * u - u^2 ≤ rho * a := by
        calc
          2 * rho * c^2 + 4 * rho * c * u - u^2
            ≤ 2 * rho * c^2 + 4 * rho^2 * c^2 := by nlinarith
          _ = 2 * rho * c^2 * (1 + 2 * rho) := by ring
          _ = 4 * rho * a * c^2 := by simp [ha] <;> ring
          _ ≤ 4 * rho * a * (1 / 4) := by gcongr <;> nlinarith
          _ = rho * a := by ring
      have h4 : b2 * (c + u)^2 + a^2 * (rho^2 - u^2) =
          a * (rho * c^2 + 2 * rho * c * u - (1 / 2 : ℝ) * u^2 + rho^2 * a) := by
        rw [hb2, ha] <;> ring
      rw [h4]
      have h6 : rho * c^2 + 2 * rho * c * u - (1 / 2 : ℝ) * u^2 ≤ rho * a / 2 := by
        linarith [h3]
      have h7 : rho * c^2 + 2 * rho * c * u - (1 / 2 : ℝ) * u^2 + rho^2 * a ≤ rho * a^2 := by
        have h8 : rho * a / 2 + rho^2 * a = rho * a^2 := by
          simp [ha] <;> ring
        linarith
      have h9 : a * (rho * c^2 + 2 * rho * c * u - (1 / 2 : ℝ) * u^2 + rho^2 * a) ≤ a * (rho * a^2) := by
        exact mul_le_mul_of_nonneg_left h7 (by positivity)
      have h10 : a * (rho * a^2) = a^2 * b2 := by
        simp [hb2] <;> ring
      rw [h10] at h9
      exact h9
    linarith
  have h_final : (c + u)^2 / a^2 + r2 / b2 ≤ 1 := by
    calc
      (c + u)^2 / a^2 + r2 / b2
        = (b2 * (c + u)^2 + a^2 * r2) / (a^2 * b2) := by
          field_simp [ha_pos.ne', hb2_pos.ne'] <;> ring
      _ ≤ (a^2 * b2) / (a^2 * b2) := by gcongr
      _ = 1 := by
        field_simp [h_pos1.ne'] <;> ring
  simpa [ha, hb2] using h_final

/-- Explicit diagonal ellipsoid map for the canonical e3-tube. -/
def canonicalEllipsoidMap (rho : ℝ) (hrho : 0 < rho) : Point3 ≃ₗ[ℝ] Point3 :=
  let a := rho + 1 / 2
  let b := Real.sqrt (rho * a)
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  { toFun := fun p => point3 (b * p 0) (b * p 1) (a * p 2)
    invFun := fun p => point3 (p 0 / b) (p 1 / b) (p 2 / a)
    left_inv := by
      intro p
      ext i
      fin_cases i <;> simp [point3] <;> field_simp [ha.ne', hb.ne'] <;> ring
    right_inv := by
      intro p
      ext i
      fin_cases i <;> simp [point3] <;> field_simp [ha.ne', hb.ne'] <;> ring
    map_add' := by
      intro p q
      ext i
      fin_cases i <;> simp [point3] <;> ring
    map_smul' := by
      intro c p
      ext i
      fin_cases i <;> simp [point3, smul_eq_mul] <;> ring }

/-- Coordinate evaluations of the canonical ellipsoid map. -/
lemma canonicalEllipsoidMap_coord0 (rho : ℝ) (hrho : 0 < rho) (p : Point3) :
    ((canonicalEllipsoidMap rho hrho) p) 0 =
      Real.sqrt (rho * (rho + 1 / 2)) * p 0 := by
  simp [canonicalEllipsoidMap, point3]

lemma canonicalEllipsoidMap_coord1 (rho : ℝ) (hrho : 0 < rho) (p : Point3) :
    ((canonicalEllipsoidMap rho hrho) p) 1 =
      Real.sqrt (rho * (rho + 1 / 2)) * p 1 := by
  simp [canonicalEllipsoidMap, point3]

lemma canonicalEllipsoidMap_coord2 (rho : ℝ) (hrho : 0 < rho) (p : Point3) :
    ((canonicalEllipsoidMap rho hrho) p) 2 = (rho + 1 / 2) * p 2 := by
  simp [canonicalEllipsoidMap, point3]

lemma canonicalEllipsoidMap_symm_coord0 (rho : ℝ) (hrho : 0 < rho) (p : Point3) :
    ((canonicalEllipsoidMap rho hrho).symm p) 0 =
      p 0 / Real.sqrt (rho * (rho + 1 / 2)) := by
  simp [canonicalEllipsoidMap, point3]

lemma canonicalEllipsoidMap_symm_coord1 (rho : ℝ) (hrho : 0 < rho) (p : Point3) :
    ((canonicalEllipsoidMap rho hrho).symm p) 1 =
      p 1 / Real.sqrt (rho * (rho + 1 / 2)) := by
  simp [canonicalEllipsoidMap, point3]

lemma canonicalEllipsoidMap_symm_coord2 (rho : ℝ) (hrho : 0 < rho) (p : Point3) :
    ((canonicalEllipsoidMap rho hrho).symm p) 2 = p 2 / (rho + 1 / 2) := by
  simp [canonicalEllipsoidMap, point3]

/-- Determinant of the canonical ellipsoid map. -/
lemma canonicalEllipsoidMap_det (rho : ℝ) (hrho : 0 < rho) :
    LinearMap.det (canonicalEllipsoidMap rho hrho).toLinearMap =
      rho * (rho + 1 / 2) ^ 2 := by
  set a : ℝ := rho + 1 / 2 with ha
  set b : ℝ := Real.sqrt (rho * a) with hb
  have hb2 : b ^ 2 = rho * a := by
    rw [hb, Real.sq_sqrt] <;> positivity
  let basis : Module.Basis (Fin 3) ℝ Point3 := PiLp.basisFun 2 ℝ (Fin 3)
  have h1 : LinearMap.det (canonicalEllipsoidMap rho hrho).toLinearMap =
      (LinearMap.toMatrix basis basis (canonicalEllipsoidMap rho hrho).toLinearMap).det := by
    rw [← LinearMap.det_toMatrix basis (canonicalEllipsoidMap rho hrho).toLinearMap]
  rw [h1]
  have h_b0 : basis 0 = point3 1 0 0 := by
    ext k; fin_cases k <;> simp [basis, PiLp.basisFun_apply, PiLp.single_apply, point3] <;> norm_num
  have h_b1 : basis 1 = point3 0 1 0 := by
    ext k; fin_cases k <;> simp [basis, PiLp.basisFun_apply, PiLp.single_apply, point3] <;> norm_num
  have h_b2 : basis 2 = point3 0 0 1 := by
    ext k; fin_cases k <;> simp [basis, PiLp.basisFun_apply, PiLp.single_apply, point3] <;> norm_num
  have hmat : (LinearMap.toMatrix basis basis (canonicalEllipsoidMap rho hrho).toLinearMap) =
      !![b, 0, 0; 0, b, 0; 0, 0, a] := by
    ext i j
    have h3 : (LinearMap.toMatrix basis basis (canonicalEllipsoidMap rho hrho).toLinearMap) i j =
        ((canonicalEllipsoidMap rho hrho) (basis j)) i := by
      simp [LinearMap.toMatrix_apply] <;> rfl
    rw [h3]
    fin_cases i <;> fin_cases j
    · simp [h_b0, canonicalEllipsoidMap_coord0 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b1, canonicalEllipsoidMap_coord0 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b2, canonicalEllipsoidMap_coord0 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b0, canonicalEllipsoidMap_coord1 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b1, canonicalEllipsoidMap_coord1 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b2, canonicalEllipsoidMap_coord1 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b0, canonicalEllipsoidMap_coord2 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b1, canonicalEllipsoidMap_coord2 rho hrho, point3] <;> norm_num <;> ring
    · simp [h_b2, canonicalEllipsoidMap_coord2 rho hrho, point3] <;> norm_num <;> ring
  rw [hmat]
  have hdet : Matrix.det (!![b, 0, 0; 0, b, 0; 0, 0, a] : Matrix (Fin 3) (Fin 3) ℝ) =
      b * b * a := by
    simp [Matrix.det_fin_three] <;> ring
  rw [hdet]
  have h9 : b * b * a = rho * a ^ 2 := by
    calc
      b * b * a = b^2 * a := by ring
      _ = (rho * a) * a := by rw [hb2]
      _ = rho * a^2 := by ring
  rw [h9, ha] <;> ring

/-- The canonical e3-tube is contained in the explicit ellipsoid. -/
lemma canonicalETube_subset_ellipsoid (rho : ℝ) (hrho : 0 < rho) :
    Metric.cthickening rho (unitSegment 0 e3) ⊆
      JohnEllipsoid.ellipsoid ((1 / 2 : ℝ) • e3) (canonicalEllipsoidMap rho hrho) := by
  intro x hx
  have h_compact : IsCompact (unitSegment (0 : Point3) e3) := by
    apply IsCompact.image
    · exact isCompact_Icc
    · continuity
  rw [h_compact.cthickening_eq_biUnion_closedBall hrho.le] at hx
  rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
  rcases hy with ⟨t, ht, rfl⟩
  have h1 : ((fun t : ℝ => (0 : Point3) + t • e3) t) = t • e3 := by simp
  have hxy' : x ∈ Metric.closedBall (t • e3) rho := by
    exact h1 ▸ hxy
  have hdist : dist x (t • e3) ≤ rho := by
    simpa [Metric.mem_closedBall] using hxy'
  have hnorm : ‖x - t • e3‖ ≤ rho := by
    have h : dist x (t • e3) = ‖x - t • e3‖ := by rw [dist_eq_norm]
    rw [h] at hdist; exact hdist
  set u : ℝ := (x - t • e3) 2 with hu
  set r2 : ℝ := (x - t • e3) 0 ^ 2 + (x - t • e3) 1 ^ 2 with hr2
  have h_norm_eq : ‖x - t • e3‖ ^ 2 = u^2 + r2 := by
    have hns : ‖x - t • e3‖ ^ 2 = ∑ i : Fin 3, ((x - t • e3) i)^2 :=
      EuclideanSpace.real_norm_sq_eq (x - t • e3)
    rw [hns]
    simp [u, r2, Fin.sum_univ_succ, e3] <;> ring
  have h_sum : u^2 + r2 ≤ rho^2 := by
    have h2 : ‖x - t • e3‖ ^ 2 ≤ rho ^ 2 := by gcongr
    rw [h_norm_eq] at h2
    exact h2
  have h_x2 : x 2 = t + u := by simp [u, e3] <;> ring
  have h_r2_eq : r2 = (x 0)^2 + (x 1)^2 := by simp [r2, e3] <;> ring
  set a : ℝ := rho + 1 / 2 with ha
  set b2 : ℝ := rho * a with hb2
  have h_ineq : (t - 1 / 2 + u)^2 / a^2 + r2 / b2 ≤ 1 :=
    ellipsoid_algebraic_ineq rho t u r2 hrho ht.1 ht.2 h_sum
  have h_ellipsoid : (x 2 - 1 / 2)^2 / a^2 + ((x 0)^2 + (x 1)^2) / b2 ≤ 1 := by
    have h9 : x 2 - 1 / 2 = t - 1 / 2 + u := by rw [h_x2] <;> ring
    have h10 : (x 0)^2 + (x 1)^2 = r2 := h_r2_eq.symm
    rw [h9, h10]
    exact h_ineq
  let Dinv := (canonicalEllipsoidMap rho hrho).symm
  set b : ℝ := Real.sqrt (rho * a) with hb_def
  have hb_pos : 0 < b := by positivity
  have hb2' : b ^ 2 = b2 := by
    rw [hb_def, Real.sq_sqrt] <;> positivity
  set y : Point3 := x - (1 / 2 : ℝ) • e3 with hy_def
  have h_eval0 : (Dinv y) 0 = (y 0) / b := by
    rw [canonicalEllipsoidMap_symm_coord0 rho hrho y, hb_def] <;> rfl
  have h_eval1 : (Dinv y) 1 = (y 1) / b := by
    rw [canonicalEllipsoidMap_symm_coord1 rho hrho y, hb_def] <;> rfl
  have h_eval2 : (Dinv y) 2 = (y 2) / a := by
    rw [canonicalEllipsoidMap_symm_coord2 rho hrho y] <;> rfl
  have h_y0 : y 0 = x 0 := by simp [hy_def, e3] <;> ring
  have h_y1 : y 1 = x 1 := by simp [hy_def, e3] <;> ring
  have h_y2 : y 2 = x 2 - 1 / 2 := by simp [hy_def, e3] <;> ring
  have h_norm2 : ‖Dinv y‖ ^ 2 = (x 2 - 1 / 2)^2 / a^2 + ((x 0)^2 + (x 1)^2) / b2 := by
    have hns : ‖Dinv y‖ ^ 2 = ∑ i : Fin 3, ((Dinv y) i)^2 :=
      EuclideanSpace.real_norm_sq_eq (Dinv y)
    rw [hns]
    have hsum : ∑ i : Fin 3, ((Dinv y) i)^2 =
        ((Dinv y) 0)^2 + ((Dinv y) 1)^2 + ((Dinv y) 2)^2 := by
      simp [Fin.sum_univ_succ] <;> ring
    rw [hsum]
    have h9 : ((Dinv y) 0)^2 + ((Dinv y) 1)^2 + ((Dinv y) 2)^2 =
        (y 0)^2 / b^2 + (y 1)^2 / b^2 + (y 2)^2 / a^2 := by
      rw [h_eval0, h_eval1, h_eval2] <;> ring
    rw [h9]
    have ha_pos : 0 < a := by positivity
    have h10 : (y 0)^2 / b^2 + (y 1)^2 / b^2 + (y 2)^2 / a^2 =
        (x 2 - 1 / 2)^2 / a^2 + ((x 0)^2 + (x 1)^2) / b2 := by
      rw [h_y0, h_y1, h_y2]
      have h12 : (x 0)^2 / b^2 + (x 1)^2 / b^2 = ((x 0)^2 + (x 1)^2) / b^2 := by
        field_simp [hb_pos.ne'] <;> ring
      rw [h12]
      have h13 : b^2 = b2 := hb2'
      rw [h13]
      <;> ring
    exact h10
  have h_norm : ‖Dinv y‖ ≤ 1 := by
    have h10 : ‖Dinv y‖ ^ 2 ≤ 1 := by
      rw [h_norm2]; exact h_ellipsoid
    have h11 : 0 ≤ ‖Dinv y‖ := by positivity
    nlinarith
  have h_in_ball : Dinv y ∈ Metric.closedBall (0 : Point3) 1 := by
    simpa [Metric.mem_closedBall] using h_norm
  have h_main : y ∈ (canonicalEllipsoidMap rho hrho) '' Metric.closedBall (0 : Point3) 1 := by
    refine ⟨Dinv y, h_in_ball, ?_⟩
    exact (canonicalEllipsoidMap rho hrho).right_inv y
  have h_eq : (1 / 2 : ℝ) • e3 + y = x := by
    rw [hy_def]
    simp [sub_eq_add_neg]
    <;> abel
  have h_final : x ∈ JohnEllipsoid.ellipsoid ((1 / 2 : ℝ) • e3) (canonicalEllipsoidMap rho hrho) := by
    rw [JohnEllipsoid.ellipsoid]
    exact ⟨y, h_main, h_eq⟩
  exact h_final

/-! ## Generalized tube containment via translation -/

/-- A tube along e3 based at `b` is contained in an ellipsoid centered at `b + (1/2)•e3`.
Proved by translating the canonical containment. -/
lemma generalizedETube_subset_ellipsoid (b : Point3) (rho : ℝ) (hrho : 0 < rho) :
    Metric.cthickening rho (unitSegment b e3) ⊆
      JohnEllipsoid.ellipsoid (b + (1 / 2 : ℝ) • e3) (canonicalEllipsoidMap rho hrho) := by
  let D := canonicalEllipsoidMap rho hrho
  intro x hx
  let y : Point3 := x - b
  let g : Point3 → Point3 := fun z => z - b
  have hg_iso : Isometry g := by
    intro z w
    simp [g, dist_eq_norm] <;> rfl
  have h_img : g '' unitSegment b e3 = unitSegment (0 : Point3) e3 := by
    ext z
    simp only [unitSegment, Set.mem_image, g]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, by simp⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨b + t • e3, ⟨t, ht, by simp⟩, ?_⟩
      simp
  have h_inf : Metric.infEDist y (unitSegment (0 : Point3) e3) = Metric.infEDist x (unitSegment b e3) := by
    have h := Metric.infEDist_image hg_iso (x := x) (t := unitSegment b e3)
    rw [h_img] at h
    exact h
  have hy : y ∈ Metric.cthickening rho (unitSegment (0 : Point3) e3) := by
    simpa [Metric.mem_cthickening_iff, h_inf] using hx
  have h_y_in : y ∈ JohnEllipsoid.ellipsoid ((1 / 2 : ℝ) • e3) D :=
    canonicalETube_subset_ellipsoid rho hrho hy
  rcases h_y_in with ⟨w, hw, h_eq⟩
  rcases hw with ⟨z, hz, rfl⟩
  have h : (b + (1 / 2 : ℝ) • e3) + D z = x := by
    have h' : ((1 / 2 : ℝ) • e3) + D z = y := h_eq
    have h1 : (b + (1 / 2 : ℝ) • e3) + D z = b + (((1 / 2 : ℝ) • e3) + D z) := by
      rw [add_assoc]
    rw [h1, h']
    have h2 : b + y = x := by
      simp [y, add_sub_cancel]
    exact h2
  exact ⟨D z, ⟨z, hz, rfl⟩, h⟩

/-! ## John ellipsoid determinant upper bound -/

/-- Image of an ellipsoid under a linear equiv. -/
lemma linearEquiv_image_ellipsoid (A : Point3 ≃ₗ[ℝ] Point3) (c : Point3)
    (D : Point3 ≃ₗ[ℝ] Point3) :
    A '' JohnEllipsoid.ellipsoid c D =
      JohnEllipsoid.ellipsoid (A c) (D.trans A) := by
  have h_unfold : ∀ (x : Point3) (E : Point3 ≃ₗ[ℝ] Point3),
      JohnEllipsoid.ellipsoid x E = (fun y : Point3 => x + E y) '' Metric.closedBall (0 : Point3) 1 := by
    intro x E
    ext z
    simp [JohnEllipsoid.ellipsoid, Set.mem_vadd_set]
    <;> constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
  rw [h_unfold c D, h_unfold (A c) (D.trans A)]
  have h_comp : A ∘ (fun y : Point3 => c + D y) = (fun y : Point3 => A c + (D.trans A) y) := by
    funext y
    simp [Function.comp_apply, A.map_add, LinearEquiv.trans_apply] <;> rfl
  have h4 : A '' ((fun y : Point3 => c + D y) '' Metric.closedBall (0 : Point3) 1) =
      (A ∘ (fun y : Point3 => c + D y)) '' Metric.closedBall (0 : Point3) 1 := by
    ext z
    simp [Set.mem_image]
    <;> constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
  rw [h4, h_comp]

/-- The outer John ellipsoid determinant of a `rho`-tube is at most `9/4`
when `rho ≤ 1`. -/
theorem tube_outerJohn_abs_det_upper {rho : ℝ} (T : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) (hrho_le_one : rho ≤ 1) :
    |LinearMap.det
      ((wz2_paper_ordinary_tube_isConvexBody T hrho).outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)| ≤ 9 / 4 := by
  set R : Point3 ≃ₗᵢ[ℝ] Point3 :=
    householderToE3 T.direction T.direction_unit with hR
  set b : Point3 := R T.base with hb
  set D : Point3 ≃ₗ[ℝ] Point3 := canonicalEllipsoidMap rho hrho with hD
  have hR_d : R T.direction = e3 := householderToE3_sends_d_to_e3 T.direction T.direction_unit
  have hR_det : |LinearMap.det (R : Point3 →ₗ[ℝ] Point3)| = 1 :=
    householderToE3_abs_det T.direction T.direction_unit

  -- R '' T.carrier = cthickening rho (unitSegment b e3)
  have h1 : R '' T.carrier = Metric.cthickening rho (unitSegment b e3) := by
    rw [Kakeya.DeltaTube.carrier, image_cthickening R,
      image_unitSegment R T.base T.direction, hR_d] <;> rfl

  -- R '' T.carrier ⊆ ellipsoid (b + (1/2)•e3) D
  have h5 : R '' T.carrier ⊆
      JohnEllipsoid.ellipsoid (b + (1 / 2 : ℝ) • e3) D := by
    rw [h1]
    exact generalizedETube_subset_ellipsoid b rho hrho

  -- Apply R.symm
  set c' : Point3 := R.symm (b + (1 / 2 : ℝ) • e3) with hc'
  set D' : Point3 ≃ₗ[ℝ] Point3 :=
    D.trans (R.symm : Point3 ≃ₗ[ℝ] Point3) with hD'
  have h6 : T.carrier ⊆ JohnEllipsoid.ellipsoid c' D' := by
    intro x hx
    have hRx : R x ∈ R '' T.carrier := ⟨x, hx, rfl⟩
    have h_in : R x ∈ JohnEllipsoid.ellipsoid (b + (1 / 2 : ℝ) • e3) D := h5 hRx
    rcases h_in with ⟨y, hy, h_eq⟩
    rcases hy with ⟨z, hz, rfl⟩
    have h4 : R.symm ((b + (1 / 2 : ℝ) • e3) + D z) = x := by
      have h5 : (b + (1 / 2 : ℝ) • e3) + D z = R x := h_eq
      rw [h5]
      exact R.left_inv x
    have h_goal : c' + D' z = x := by
      have h51 : c' + D' z = R.symm (b + (1 / 2 : ℝ) • e3) + R.symm (D z) := by
        simp [c', D', LinearEquiv.trans_apply] <;> rfl
      rw [h51]
      have h52 : R.symm (b + (1 / 2 : ℝ) • e3) + R.symm (D z) =
          R.symm ((b + (1 / 2 : ℝ) • e3) + D z) := by
        rw [← R.symm.map_add] <;> rfl
      rw [h52, h4]
    have h_vadd : c' +ᵥ D' z = x := by
      have h : c' +ᵥ D' z = c' + D' z := by
        exact PiLp.ext (congrFun rfl)
      rw [h, h_goal]
    exact ⟨D' z, ⟨z, hz, rfl⟩, h_vadd⟩

  -- John minimality
  let hK := wz2_paper_ordinary_tube_isConvexBody T hrho
  let center := hK.outerJohnEllipsoidCenter
  let JohnMap := hK.outerJohnEllipsoidMap
  have hJohn : JohnEllipsoid.IsOuterJohnEllipsoid T.carrier center JohnMap :=
    hK.outerJohnEllipsoid_spec
  let ball := Metric.closedBall (0 : Point3) 1
  have hmin : volume (JohnEllipsoid.ellipsoid center JohnMap) ≤
      volume (JohnEllipsoid.ellipsoid c' D') := hJohn.2 c' D' h6

  -- Volume formulas
  have hvol1 : volume (JohnEllipsoid.ellipsoid center JohnMap) =
      ENNReal.ofReal |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| * volume ball := by
    rw [JohnEllipsoid.volume_ellipsoid_eq]
  have hvol2 : volume (JohnEllipsoid.ellipsoid c' D') =
      ENNReal.ofReal |LinearMap.det (D' : Point3 →ₗ[ℝ] Point3)| * volume ball := by
    rw [JohnEllipsoid.volume_ellipsoid_eq]

  -- Ball has positive volume
  have hball_pos : 0 < volume ball := by
    have h_open : IsOpen (Metric.ball (0 : Point3) (1 / 2 : ℝ)) := isOpen_ball
    have h_nonempty : (Metric.ball (0 : Point3) (1 / 2 : ℝ)).Nonempty := ⟨0, by norm_num⟩
    have h9 : 0 < volume (Metric.ball (0 : Point3) (1 / 2 : ℝ)) :=
      h_open.measure_pos volume h_nonempty
    have h10 : Metric.ball (0 : Point3) (1 / 2 : ℝ) ⊆ ball := by
      intro x hx
      have h11 : dist x 0 < 1 / 2 := hx
      have h12 : dist x 0 ≤ 1 := by linarith
      simpa [ball, Metric.mem_closedBall] using h12
    exact h9.trans_le (measure_mono h10)
  have hball_lt_top : volume ball < ⊤ := by
    have h : IsCompact (ball : Set Point3) := isCompact_closedBall _ _
    exact measure_closedBall_lt_top
  have hball_ne_top : volume ball ≠ ⊤ := hball_lt_top.ne

  -- Cancel ball volume
  rw [hvol1, hvol2] at hmin
  have hcancel : ENNReal.ofReal |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| ≤
      ENNReal.ofReal |LinearMap.det (D' : Point3 →ₗ[ℝ] Point3)| := by
    by_contra h
    have h' : ENNReal.ofReal |LinearMap.det (D' : Point3 →ₗ[ℝ] Point3)| <
        ENNReal.ofReal |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| := lt_of_not_ge h
    have hball_ne_zero : volume ball ≠ 0 := hball_pos.ne'
    set x := ENNReal.ofReal |LinearMap.det (D' : Point3 →ₗ[ℝ] Point3)|
    set y := ENNReal.ofReal |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)|
    have h_lt : volume ball * x < volume ball * y :=
      ENNReal.mul_lt_mul_right hball_ne_zero hball_ne_top h'
    have hcomm1 : volume ball * x = x * volume ball := by rw [mul_comm]
    have hcomm2 : volume ball * y = y * volume ball := by rw [mul_comm]
    rw [hcomm1, hcomm2] at h_lt
    exact False.elim (not_le.mpr h_lt hmin)

  -- Determinant of D'
  have hdetD' : |LinearMap.det (D' : Point3 →ₗ[ℝ] Point3)| =
      |LinearMap.det (D : Point3 →ₗ[ℝ] Point3)| := by
    have h_eq1 : (D' : Point3 →ₗ[ℝ] Point3) =
        (R.symm : Point3 →ₗ[ℝ] Point3).comp (D : Point3 →ₗ[ℝ] Point3) := by
      ext y
      simp [D', LinearEquiv.trans_apply] <;> rfl
    rw [h_eq1, LinearMap.det_comp]
    have hR_symm_abs : |LinearMap.det ((R.symm : Point3 →ₗ[ℝ] Point3))| = 1 := by
      have hne : LinearMap.det (R : Point3 →ₗ[ℝ] Point3) ≠ 0 :=
        (LinearEquiv.isUnit_det' R.toLinearEquiv).ne_zero
      have h1 : LinearMap.det ((R.symm : Point3 →ₗ[ℝ] Point3)) * LinearMap.det (R : Point3 →ₗ[ℝ] Point3) = 1 := by
        have hcomp : ((R.symm : Point3 →ₗ[ℝ] Point3).comp (R : Point3 →ₗ[ℝ] Point3)) = LinearMap.id := by
          ext z; simp
        have h2 := congr_arg LinearMap.det hcomp
        simpa [LinearMap.det_comp, LinearMap.det_id] using h2
      have h1' : LinearMap.det (R : Point3 →ₗ[ℝ] Point3) * LinearMap.det ((R.symm : Point3 →ₗ[ℝ] Point3)) = 1 := by
        rw [mul_comm] at h1
        exact h1
      have h3 : LinearMap.det ((R.symm : Point3 →ₗ[ℝ] Point3)) = (LinearMap.det (R : Point3 →ₗ[ℝ] Point3))⁻¹ := by
        apply (mul_right_inj' hne).mp
        rw [h1']
        exact (mul_inv_cancel₀ hne).symm
      rw [h3, abs_inv, hR_det] <;> norm_num
    rw [abs_mul, hR_symm_abs] <;> ring

  -- Determinant of D
  have hdetD : |LinearMap.det (D : Point3 →ₗ[ℝ] Point3)| =
      rho * (rho + 1 / 2) ^ 2 := by
    have hpos : 0 < rho * (rho + 1 / 2) ^ 2 := by positivity
    rw [canonicalEllipsoidMap_det rho hrho]
    rw [abs_of_pos hpos]

  -- Final bound
  rw [hdetD', hdetD] at hcancel
  have hreal : |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| ≤ rho * (rho + 1 / 2) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcancel
  have hbound : rho * (rho + 1 / 2) ^ 2 ≤ 9 / 4 := by
    nlinarith [sq_nonneg (rho - 1), hrho_le_one, hrho]
  exact le_trans hreal hbound

/-! ## Normalized volume lower bound -/

/-- Volume of the normalized fine tube is at least `4πδ²/9`. -/
theorem single_tube_normalized_volume_lower {delta rho : ℝ}
    (fineT : Kakeya.DeltaTube delta) (coarseT : Kakeya.DeltaTube rho)
    (normalization : WZ2PaperAssouadUnitRescalingData coarseT)
    (hdelta_pos : 0 < delta) (hrho : 0 < rho) (hrho_le_one : rho ≤ 1) :
    ENNReal.ofReal (4 * Real.pi * delta^2 / 9) ≤
      volume (normalization.map '' fineT.carrier) := by
  let JohnMap := normalization.parent_convex_body.outerJohnEllipsoidMap

  -- Volume of normalized fine tube
  have hvol_norm : volume (normalization.map '' fineT.carrier) =
      ENNReal.ofReal |LinearMap.det (normalization.map.linear : Point3 →ₗ[ℝ] Point3)| *
        volume fineT.carrier :=
    wz2PaperAffineEquiv_volume_image_eq normalization.map fineT.carrier

  -- |det(normalization.map.linear)| = 1 / |det JohnMap|
  have hdet_norm : |LinearMap.det (normalization.map.linear : Point3 →ₗ[ℝ] Point3)| =
      1 / |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| := by
    have h1 : (normalization.map.linear : Point3 →ₗ[ℝ] Point3) =
        (JohnMap.symm : Point3 →ₗ[ℝ] Point3) := by
      rfl
    rw [h1]
    have h2 : LinearMap.det (JohnMap.symm : Point3 →ₗ[ℝ] Point3) =
        (LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3))⁻¹ := by
      have h3 : LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3) * LinearMap.det (JohnMap.symm : Point3 →ₗ[ℝ] Point3) = 1 := by
        have h4 : ((JohnMap : Point3 →ₗ[ℝ] Point3).comp (JohnMap.symm : Point3 →ₗ[ℝ] Point3)) = .id := by
          ext x; simp
        have h5 := congr_arg LinearMap.det h4
        rw [LinearMap.det_comp, LinearMap.det_id] at h5
        exact h5
      have h6 : LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3) ≠ 0 := by
        intro h7
        rw [h7] at h3
        norm_num at h3
      field_simp [h6] <;> linarith
    rw [h2, abs_inv]
    <;> field_simp

  -- |det JohnMap| ≤ 9/4
  have hdet_upper : |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| ≤ 9 / 4 :=
    tube_outerJohn_abs_det_upper coarseT hrho hrho_le_one

  -- |det JohnMap| > 0
  have hdet_pos : 0 < |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| := by
    have hne : LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3) ≠ 0 := by
      have h3 : LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3) * LinearMap.det (JohnMap.symm : Point3 →ₗ[ℝ] Point3) = 1 := by
        have h4 : ((JohnMap : Point3 →ₗ[ℝ] Point3).comp (JohnMap.symm : Point3 →ₗ[ℝ] Point3)) = .id := by
          ext x; simp
        have h5 := congr_arg LinearMap.det h4
        rw [LinearMap.det_comp, LinearMap.det_id] at h5
        exact h5
      intro h7
      rw [h7] at h3
      norm_num at h3
    exact abs_pos.mpr hne

  -- 1/|det JohnMap| ≥ 4/9
  have hdet_lower : 4 / 9 ≤ 1 / |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| := by
    have h : 1 / |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)| ≥ 1 / (9 / 4 : ℝ) := by
      gcongr
    have h2 : (1 / (9 / 4 : ℝ)) = 4 / 9 := by norm_num
    rw [h2] at h
    exact h

  -- Volume of fine tube ≥ πδ²
  have hvol_fine : ENNReal.ofReal (Real.pi * delta^2) ≤ volume fineT.carrier := by
    let canonical : Kakeya.DeltaTube delta :=
      { base := 0
        direction := EuclideanSpace.single 0 1
        direction_unit := by simp }
    have h : volume fineT.carrier = volume canonical.carrier :=
      Kakeya.Streamlined.tube_volume_eq fineT canonical
    have hcanon : volume canonical.carrier = Kakeya.deltaTubeVolume delta := by rfl
    rw [h, hcanon]
    exact deltaTubeVolume_lower_pi hdelta_pos

  -- Combine
  rw [hvol_norm, hdet_norm]
  have h1 : ENNReal.ofReal (4 / 9 : ℝ) * ENNReal.ofReal (Real.pi * delta^2) ≤
      ENNReal.ofReal (1 / |LinearMap.det (JohnMap : Point3 →ₗ[ℝ] Point3)|) *
        volume fineT.carrier := by
    exact mul_le_mul'
      (ENNReal.ofReal_le_ofReal hdet_lower)
      hvol_fine
  have h2 : ENNReal.ofReal (4 / 9 : ℝ) * ENNReal.ofReal (Real.pi * delta^2) =
      ENNReal.ofReal (4 * Real.pi * delta^2 / 9) := by
    rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
  rw [h2] at h1
  exact h1

/-! ## Convex Wolff bound for one-body family -/

/-- Convex-Wolff bound for a one-body family with volume ≥ `4πδ²/9`
and `C ≥ δ^(-2)`. -/
lemma one_body_convex_wolff {delta : ℝ}
    (B : Kakeya.Streamlined.BodyFamily)
    (hcard : B.card = 1)
    (C : ENNReal)
    (hC_ge_delta_inv2 : ENNReal.ofReal (delta ^ (-2 : ℝ)) ≤ C)
    (hdelta_pos : 0 < delta)
    (hvol : ∀ (i : Fin B.card),
      ENNReal.ofReal (4 * Real.pi * delta^2 / 9) ≤ (B.body i).volume) :
    WZ2PaperBodyConvexWolffBound B C := by
  intro convexSet hconv
  have h_enncard : B.enncard = 1 := by
    simp [Kakeya.Streamlined.BodyFamily.enncard, hcard] <;> norm_num
  rw [h_enncard]

  have hpos : 0 < B.card := by rw [hcard] <;> norm_num
  let z : Fin B.card := ⟨0, hpos⟩

  let idxSet := B.containedIndices convexSet
  have hle : idxSet.card ≤ 1 := by
    have h : idxSet ⊆ (Finset.univ : Finset (Fin B.card)) := Finset.subset_univ _
    have h2 : (Finset.univ : Finset (Fin B.card)).card = B.card := by simp
    have h3 : idxSet.card ≤ (Finset.univ : Finset (Fin B.card)).card := Finset.card_le_card h
    have h4 : idxSet.card ≤ B.card := by linarith
    have h5 : B.card = 1 := hcard
    omega

  by_cases h0 : idxSet.card = 0
  · have h_empty : B.containedIndices convexSet = ∅ := Finset.card_eq_zero.mp h0
    have hcount : B.containedCount convexSet = 0 := by
      have h : B.containedCount convexSet = ↑((B.containedIndices convexSet).card) := by rfl
      rw [h, h_empty]
      <;> simp
    rw [hcount]
    <;> simp
    <;> exact zero_le _
  · have hne : idxSet.card ≠ 0 := h0
    have h1 : idxSet.card = 1 := by
      omega
    have h2 : z ∈ idxSet := by
      have h3 : idxSet.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      rcases h3 with ⟨j, hj⟩
      have h4 : j = z := by
        have h5 : (j : ℕ) < B.card := j.is_lt
        have h6 : (j : ℕ) = 0 := by omega
        apply Fin.ext; exact h6
      rw [h4] at hj; exact hj
    have h2' : z ∈ B.containedIndices convexSet := h2
    have hbody : (B.body z).carrier ⊆ convexSet := by
      simpa using h2'
    have hcount : B.containedCount convexSet = 1 := by
      have h : B.containedCount convexSet = (idxSet.card : ENNReal) := by
        rfl
      rw [h, h1]
      <;> norm_num
    rw [hcount]
    have hvol2 : (B.body z).volume ≤ volume convexSet := measure_mono hbody
    have h4 : (1 : ENNReal) ≤ C * (B.body z).volume := by
      have h5 : C * (B.body z).volume ≥
          ENNReal.ofReal (delta ^ (-2 : ℝ)) * ENNReal.ofReal (4 * Real.pi * delta^2 / 9) :=
        mul_le_mul' hC_ge_delta_inv2 (hvol z)
      have h6 : ENNReal.ofReal (delta ^ (-2 : ℝ)) * ENNReal.ofReal (4 * Real.pi * delta^2 / 9) =
          ENNReal.ofReal (4 * Real.pi / 9) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        have h7 : delta ^ (-2 : ℝ) * (4 * Real.pi * delta^2 / 9) = 4 * Real.pi / 9 := by
          simp [Real.rpow_neg, Real.rpow_two]
          <;> field_simp [hdelta_pos.ne'] <;> ring
        rw [h7]
      have h5' : ENNReal.ofReal (4 * Real.pi / 9) ≤ C * (B.body z).volume := by
        rw [← h6]
        exact h5
      have h7 : (1 : ℝ) ≤ 4 * Real.pi / 9 := by
        have h8 : Real.pi > 3 := Real.pi_gt_three
        linarith
      have h9 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
      have h10 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (4 * Real.pi / 9) :=
        ENNReal.ofReal_le_ofReal h7
      have h11 : (1 : ENNReal) ≤ ENNReal.ofReal (4 * Real.pi / 9) := by
        rw [h9] <;> exact h10
      exact h11.trans h5'
    have h10 : (1 : ENNReal) ≤ C * volume convexSet := by
      calc (1 : ENNReal)
        ≤ C * (B.body z).volume := h4
      _ ≤ C * volume convexSet := by gcongr
    simpa using h10

/-! ## Full nearby-scales CWA -/

/-- Nearby-scales CWA for a single-tube family via self-cover. -/
theorem single_tube_cwa_nearby {delta outputLoss : ℝ}
    (T : Kakeya.DeltaTube delta)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (houtputLoss_ge_two : 2 ≤ outputLoss)
    (hdelta_small : delta ≤ 1 / 12) :
    WZ2PaperPureCWAAtNearbyScales
      ({ card := 1, tube := fun (_ : Fin 1) => T } : Kakeya.Streamlined.TubeFamily delta)
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  let C : ENNReal := Kakeya.realRpowENN delta (-outputLoss)
  let fineFamily : Kakeya.Streamlined.TubeFamily delta :=
    { card := 1, tube := fun _ => T }

  -- C ≥ δ^(-2)
  have hC_ge_delta_inv2 : ENNReal.ofReal (delta ^ (-2 : ℝ)) ≤ C := by
    have h1 : delta ^ (-2 : ℝ) ≤ delta ^ (-outputLoss) := by
      apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one <;> linarith
    have hC : C = ENNReal.ofReal (delta ^ (-outputLoss)) := by
      simp [C, Kakeya.realRpowENN] <;> rfl
    rw [hC]
    exact ENNReal.ofReal_le_ofReal h1

  -- C > 1
  have hC_gt_one : (1 : ENNReal) < C := by
    have h1 : (1 : ℝ) < delta ^ (-outputLoss) := by
      have h2 : delta ^ (-outputLoss) ≥ delta ^ (-2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one <;> linarith
      have h3 : delta ^ (-2 : ℝ) = 1 / (delta ^ 2) := by
        simp [Real.rpow_neg, Real.rpow_two] <;> field_simp [hdelta_pos.ne'] <;> ring
      have h4 : (1 : ℝ) < 1 / (delta ^ 2) := by
        have h5 : 0 < delta ^ 2 := by positivity
        have h6 : delta ^ 2 < 1 := by nlinarith
        exact one_lt_one_div h5 h6
      linarith [h2, h3, h4]
    have hC : C = ENNReal.ofReal (delta ^ (-outputLoss)) := by
      simp [C, Kakeya.realRpowENN] <;> rfl
    rw [hC]
    have h9 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h9]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h1

  -- Finite error constant
  have hC_le_one : (1 : ENNReal) ≤ C := le_of_lt hC_gt_one
  have hfec : WZ2PaperFiniteErrorConstant C :=
    ⟨hC_le_one, ENNReal.ofReal_ne_top⟩

  -- Essential distinctness (vacuous)
  have hed : WZ2PaperOrdinaryIsEssentiallyDistinct fineFamily := by
    intro first second hne
    exfalso
    have h1 : (first : ℕ) = 0 := by fin_cases first <;> rfl
    have h2 : (second : ℕ) = 0 := by fin_cases second <;> rfl
    have h3 : first = second := by apply Fin.ext; rw [h1, h2]
    exact hne h3

  refine ⟨hdelta_pos, hfec, hed, fun rho₀ => ?_⟩
  let rho : ℝ := rho₀.1
  have hdelta_le_rho : delta ≤ rho := rho₀.2.1
  have hrho_le_one : rho ≤ 1 := rho₀.2.2
  have hrho_pos : 0 < rho := lt_of_lt_of_le hdelta_pos hdelta_le_rho

  -- Coarse tube (same base/direction, radius rho)
  let coarseT : Kakeya.DeltaTube rho :=
    { base := T.base
      direction := T.direction
      direction_unit := T.direction_unit }
  let coarseFamily : Kakeya.Streamlined.TubeFamily rho :=
    { card := 1, tube := fun _ => coarseT }

  -- Fine tube ⊆ coarse tube
  have hfine_sub : T.carrier ⊆ coarseT.carrier := by
    dsimp only [Kakeya.DeltaTube.carrier]
    intro x hx
    simpa [Metric.mem_cthickening_iff] using hx.trans (ENNReal.ofReal_le_ofReal (by linarith))

  -- Fiber indices = {0}
  have hfiber_set : wz2PaperOrdinaryFullFiberIndices fineFamily coarseFamily (0 : Fin 1) =
      ({0} : Finset (Fin 1)) := by
    ext j
    simp [wz2PaperOrdinaryFullFiberIndices, mem_wz2PaperOrdinaryFullFiberIndices_iff,
      fineFamily, coarseFamily, hfine_sub]
    <;> fin_cases j <;> simp

  -- Cover
  let cover : WZ2PaperPurePartitioningCover fineFamily coarseFamily :=
    { covers := by
        intro source
        have hsrc : source = 0 := by fin_cases source <;> rfl
        refine ⟨(0 : Fin coarseFamily.card), ?_⟩
        have h_goal : source ∈ wz2PaperOrdinaryFullFiberIndices fineFamily coarseFamily (0 : Fin coarseFamily.card) := by
          have h : source = 0 := hsrc
          rw [h]
          have h' : (0 : Fin fineFamily.card) ∈ wz2PaperOrdinaryFullFiberIndices fineFamily coarseFamily (0 : Fin coarseFamily.card) := by
            simpa [mem_wz2PaperOrdinaryFullFiberIndices_iff] using hfine_sub
          exact h'
        exact h_goal
      doubled_fibers_disjoint := by
        intro first second hne
        exfalso
        have h1 : (first : ℕ) = 0 := by fin_cases first <;> rfl
        have h2 : (second : ℕ) = 0 := by fin_cases second <;> rfl
        have h3 : first = second := by apply Fin.ext; rw [h1, h2]
        exact hne h3 }

  -- Full fiber uniform
  have hffu : WZ2PaperPureFullFibersAreCUniform fineFamily coarseFamily C := by
    intro first second
    have h1 : first = 0 := by fin_cases first <;> rfl
    have h2 : second = 0 := by fin_cases second <;> rfl
    rw [h1, h2]
    have hfiber : wz2PaperOrdinaryFullFiberCount fineFamily coarseFamily (0 : Fin 1) = 1 := by
      rw [wz2PaperOrdinaryFullFiberCount, hfiber_set] <;> simp
    rw [hfiber]
    have hC1 : (1 : ENNReal) ≤ C := le_of_lt hC_gt_one
    simpa using hC1

  -- Rescaled fiber
  have hrf : ∀ (parent : Fin coarseFamily.card),
      Nonempty (WZ2PaperPureUnitRescaledFullFiberData
        (fine := fineFamily) (coarse := coarseFamily) (parent := parent) C) := by
    intro parent
    have hp : parent = 0 := by fin_cases parent <;> rfl
    subst hp
    let normalization := WZ2PaperAssouadUnitRescalingData.ofTube coarseT hrho_pos
    let bodyFamily := wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := fineFamily) (coarse := coarseFamily) (parent := (0 : Fin coarseFamily.card)) normalization
    have hbf_card : bodyFamily.card = 1 := by
      simp [bodyFamily, wz2PaperPureUnitRescaledFullFiberBodyFamily, hfiber_set] <;> norm_num
    have hbf_pos : 0 < bodyFamily.card := by rw [hbf_card] <;> norm_num
    let z : Fin bodyFamily.card := ⟨0, hbf_pos⟩
    have hbf_vol : ∀ (i : Fin bodyFamily.card),
        ENNReal.ofReal (4 * Real.pi * delta^2 / 9) ≤ (bodyFamily.body i).volume := by
      intro i
      have hi : i = z := by
        apply Fin.ext
        have h : (i : ℕ) < bodyFamily.card := i.is_lt
        have hcard : bodyFamily.card = 1 := hbf_card
        have h' : (i : ℕ) = 0 := by omega
        exact h'
      rw [hi]
      simp [bodyFamily, wz2PaperPureUnitRescaledFullFiberBodyFamily, hfiber_set, z]
      <;> exact single_tube_normalized_volume_lower T coarseT normalization hdelta_pos hrho_pos hrho_le_one
    let hcw : WZ2PaperBodyConvexWolffBound bodyFamily C :=
      one_body_convex_wolff bodyFamily hbf_card C hC_ge_delta_inv2 hdelta_pos hbf_vol
    let fiberData : WZ2PaperPureUnitRescaledFullFiberData
        (fine := fineFamily) (coarse := coarseFamily) (parent := (0 : Fin coarseFamily.card)) C :=
      { normalization := normalization
        convex_wolff := hcw }
    exact ⟨fiberData⟩

  -- Scale data
  let scaleData : WZ2PaperPureScaleCoverData fineFamily rho C :=
    { delta_pos := hdelta_pos
      rho_pos := hrho_pos
      coarse := coarseFamily
      cover := cover
      full_fiber_uniform := hffu
      rescaledFiber := hrf }

  -- Within factor: rho = rho₀, so need 1 < C
  have hwf : ENNReal.ofReal rho < C * ENNReal.ofReal rho₀.1 := by
    have hrho_pos' : 0 < rho := hrho_pos
    have hne_zero : ENNReal.ofReal rho ≠ 0 := by
      have hpos : 0 < ENNReal.ofReal rho := ENNReal.ofReal_pos.mpr hrho_pos'
      exact hpos.ne'
    have hne_top : ENNReal.ofReal rho ≠ ⊤ := ENNReal.ofReal_ne_top
    have h : ENNReal.ofReal rho * (1 : ENNReal) < ENNReal.ofReal rho * C :=
      ENNReal.mul_lt_mul_right hne_zero hne_top hC_gt_one
    have h' : (1 : ENNReal) * ENNReal.ofReal rho < C * ENNReal.ofReal rho := by
      have h1 : (1 : ENNReal) * ENNReal.ofReal rho = ENNReal.ofReal rho * (1 : ENNReal) := by
        rw [mul_comm]
      have h2 : C * ENNReal.ofReal rho = ENNReal.ofReal rho * C := by rw [mul_comm]
      rw [h1, h2]
      exact h
    simpa using h'

  -- Nearby scale cover data
  let nearbyData : WZ2PaperPureNearbyScaleCoverData fineFamily rho₀ C :=
    { rho := rho
      requested_le := by linarith
      within_factor := hwf
      scaleData := scaleData }

  exact ⟨nearbyData⟩

end Kakeya.Assouad

end
