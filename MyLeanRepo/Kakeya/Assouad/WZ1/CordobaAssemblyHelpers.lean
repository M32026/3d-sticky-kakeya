import MyLeanRepo.Kakeya.Assouad.WZ1.CubeCountGeometry

/-!
# Helper lemmas for the Córdoba slab assembly

1. `tube_ball_intersection_volume_simple`: volume of a δ-tube ∩ ball of radius R
   is ≤ 8*δ²*R.
2. `property_one_mass_in_3tau_ball`: transfer propertyOne_full volume bound
   from a τ-ball to a 3τ-ball.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya MeasureTheory Metric

/-- Volume of a δ-tube intersected with a ball of radius R is ≤ 8*δ²*R.

Uses the three-diameter bound: axial diameter ≤ 2R (from the ball),
transverse diameters ≤ 2δ (from the tube radius). -/
lemma tube_ball_intersection_volume_simple
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (T : DeltaTube δ) (q : Point3) :
    volume (T.carrier ∩ closedBall q R) ≤
      ENNReal.ofReal (8 * δ^2 * R) := by
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1_std : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2_std : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  have he0_norm : ‖e0_std‖ = 1 := by simp [e0_std]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (T.direction - e0_std))ᗮ
  have hA : A T.direction = e0_std :=
    Submodule.reflection_sub (by rw [T.direction_unit, he0_norm])
  let e2 : Point3 := A.symm e1_std
  let e3 : Point3 := A.symm e2_std
  have he2_norm : ‖e2‖ = 1 := by
    have h : ‖e2‖ = ‖e1_std‖ := A.symm.norm_map e1_std
    rw [h] ; simp [e1_std]
  have he3_norm : ‖e3‖ = 1 := by
    have h : ‖e3‖ = ‖e2_std‖ := A.symm.norm_map e2_std
    rw [h] ; simp [e2_std]
  have he2_orth : inner ℝ T.direction e2 = 0 := by
    have h : inner ℝ T.direction e2 = inner ℝ (A T.direction) (A e2) := (A.inner_map_map T.direction e2).symm
    rw [h, hA]
    have hAe2 : A e2 = e1_std := by simp [e2]
    rw [hAe2]
    have h_zero : inner ℝ e0_std e1_std = 0 := by
      have h_symm : inner ℝ e0_std e1_std = inner ℝ e1_std e0_std :=
        (real_inner_comm e0_std e1_std).symm
      rw [h_symm]
      have h : inner ℝ e1_std e0_std = (1 : ℝ) * e1_std 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) e1_std
      rw [h]
      have h2 : e1_std 0 = 0 := by
        simp [e1_std]
      rw [h2] ; ring
    exact h_zero
  have he3_orth : inner ℝ T.direction e3 = 0 := by
    have h : inner ℝ T.direction e3 = inner ℝ (A T.direction) (A e3) := (A.inner_map_map T.direction e3).symm
    rw [h, hA]
    have hAe3 : A e3 = e2_std := by simp [e3]
    rw [hAe3]
    have h_zero : inner ℝ e0_std e2_std = 0 := by
      have h_symm : inner ℝ e0_std e2_std = inner ℝ e2_std e0_std :=
        (real_inner_comm e0_std e2_std).symm
      rw [h_symm]
      have h : inner ℝ e2_std e0_std = (1 : ℝ) * e2_std 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) e2_std
      rw [h]
      have h2 : e2_std 0 = 0 := by
        simp [e2_std]
      rw [h2] ; ring
    exact h_zero
  have hcoord0 : ∀ (z : Point3), (A z) 0 = inner ℝ z T.direction := by
    intro z
    have h : (A z) 0 = inner ℝ (A z) e0_std := by
      have h2 : inner ℝ (A z) e0_std = (1 : ℝ) * (A z) 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) (A z)
      rw [h2] ; ring
    rw [h]
    have h3 : inner ℝ (A z) e0_std = inner ℝ z (A.symm e0_std) := by
      have h4 := A.inner_map_map z (A.symm e0_std)
      have h5 : A (A.symm e0_std) = e0_std := A.apply_symm_apply e0_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e0_std = T.direction := by
      have h7 : A (A.symm e0_std) = A T.direction := by rw [A.apply_symm_apply, hA]
      exact A.injective h7
    rw [h6]
  have hcoord1 : ∀ (z : Point3), (A z) 1 = inner ℝ z e2 := by
    intro z
    have h : (A z) 1 = inner ℝ (A z) e1_std := by
      have h2 : inner ℝ (A z) e1_std = (1 : ℝ) * (A z) 1 :=
        EuclideanSpace.inner_single_right 1 (1 : ℝ) (A z)
      rw [h2] ; ring
    rw [h]
    have h3 : inner ℝ (A z) e1_std = inner ℝ z (A.symm e1_std) := by
      have h4 := A.inner_map_map z (A.symm e1_std)
      have h5 : A (A.symm e1_std) = e1_std := A.apply_symm_apply e1_std
      rw [h5] at h4; exact h4
    rw [h3]
  have hcoord2 : ∀ (z : Point3), (A z) 2 = inner ℝ z e3 := by
    intro z
    have h : (A z) 2 = inner ℝ (A z) e2_std := by
      have h2 : inner ℝ (A z) e2_std = (1 : ℝ) * (A z) 2 :=
        EuclideanSpace.inner_single_right 2 (1 : ℝ) (A z)
      rw [h2] ; ring
    rw [h]
    have h3 : inner ℝ (A z) e2_std = inner ℝ z (A.symm e2_std) := by
      have h4 := A.inner_map_map z (A.symm e2_std)
      have h5 : A (A.symm e2_std) = e2_std := A.apply_symm_apply e2_std
      rw [h5] at h4; exact h4
    rw [h3]
  let S : Set Point3 := T.carrier ∩ closedBall q R
  let d0 : ℝ := 2 * R
  let d1 : ℝ := 2 * δ
  let d2 : ℝ := 2 * δ
  have hd0_nonneg : 0 ≤ d0 := by positivity
  have hd1_nonneg : 0 ≤ d1 := by positivity
  have hd2_nonneg : 0 ≤ d2 := by positivity
  have h0 : ∀ x y, x ∈ S → y ∈ S → |(A x) 0 - (A y) 0| ≤ d0 := by
    intro x y hx hy
    rw [hcoord0 x, hcoord0 y]
    have h_sub : inner ℝ x T.direction - inner ℝ y T.direction = inner ℝ (x - y) T.direction := by
      rw [inner_sub_left]
    rw [h_sub]
    have hcs : |inner ℝ (x - y) T.direction| ≤ ‖x - y‖ := by
      have h : |inner ℝ (x - y) T.direction| ≤ ‖x - y‖ * ‖T.direction‖ :=
        abs_real_inner_le_norm (x - y) T.direction
      rw [T.direction_unit] at h
      simpa using h
    have hxq : dist x q ≤ R := by simpa [Metric.mem_closedBall] using hx.2
    have hyq : dist y q ≤ R := by simpa [Metric.mem_closedBall, dist_comm] using hy.2
    have hqy : dist q y ≤ R := by rwa [dist_comm]
    have hdist : dist x y ≤ 2 * R := by
      calc dist x y ≤ dist x q + dist q y := dist_triangle x q y
        _ ≤ R + R := by linarith
        _ = 2 * R := by ring
    have hnorm : ‖x - y‖ ≤ 2 * R := by simpa [dist_eq_norm] using hdist
    exact le_trans hcs hnorm
  have h1 : ∀ x y, x ∈ S → y ∈ S → |(A x) 1 - (A y) 1| ≤ d1 := by
    intro x y hx hy
    rw [hcoord1 x, hcoord1 y]
    have hbx : |inner ℝ (x - T.base) e2| ≤ δ :=
      tube_perpendicular_projection_bound (by linarith) T e2 he2_norm he2_orth x hx.1
    have hby : |inner ℝ (y - T.base) e2| ≤ δ :=
      tube_perpendicular_projection_bound (by linarith) T e2 he2_norm he2_orth y hy.1
    have h : inner ℝ x e2 - inner ℝ y e2 = inner ℝ (x - T.base) e2 - inner ℝ (y - T.base) e2 := by
      simp [inner_sub_left]
    rw [h]
    have h2 : |inner ℝ (x - T.base) e2 - inner ℝ (y - T.base) e2| ≤
        |inner ℝ (x - T.base) e2| + |inner ℝ (y - T.base) e2| := by
      exact abs_sub _ _
    linarith
  have h2 : ∀ x y, x ∈ S → y ∈ S → |(A x) 2 - (A y) 2| ≤ d2 := by
    intro x y hx hy
    rw [hcoord2 x, hcoord2 y]
    have hbx : |inner ℝ (x - T.base) e3| ≤ δ :=
      tube_perpendicular_projection_bound (by linarith) T e3 he3_norm he3_orth x hx.1
    have hby : |inner ℝ (y - T.base) e3| ≤ δ :=
      tube_perpendicular_projection_bound (by linarith) T e3 he3_norm he3_orth y hy.1
    have h : inner ℝ x e3 - inner ℝ y e3 = inner ℝ (x - T.base) e3 - inner ℝ (y - T.base) e3 := by
      simp [inner_sub_left]
    rw [h]
    have h2 : |inner ℝ (x - T.base) e3 - inner ℝ (y - T.base) e3| ≤
        |inner ℝ (x - T.base) e3| + |inner ℝ (y - T.base) e3| := by
      exact abs_sub _ _
    linarith
  have hS_meas : MeasurableSet S :=
    (Metric.isClosed_cthickening).measurableSet.inter Metric.isClosed_closedBall.measurableSet
  have hvol : volume S ≤ ENNReal.ofReal (d0 * d1 * d2) :=
    volume_by_three_diameters_public hS_meas A d0 d1 d2 hd0_nonneg hd1_nonneg hd2_nonneg h0 h1 h2
  have h_expr : d0 * d1 * d2 = 8 * δ^2 * R := by
    dsimp only [d0, d1, d2] ; ring
  rw [h_expr] at hvol
  exact hvol

/-- Transfer a volume lower bound from a τ-ball to a 3τ-ball.

If a set `A` has volume ≥ `V` in `closedBall p τ`, and `p ∈ closedBall q τ`,
then `A` has volume ≥ `V` in `closedBall q (3τ)`. -/
lemma volume_ball_expand
    {A : Set Point3} {V : ENNReal} (p q : Point3) (tau : ℝ) (htau_pos : 0 < tau)
    (hp_ball : p ∈ Metric.closedBall q tau)
    (hV : volume (A ∩ Metric.closedBall p tau) ≥ V) :
    volume (A ∩ Metric.closedBall q (3 * tau)) ≥ V := by
  have h1 : Metric.closedBall p tau ⊆ Metric.closedBall q (3 * tau) := by
    intro x hx
    have hxp : dist x p ≤ tau := by simpa [Metric.mem_closedBall] using hx
    have hpq : dist p q ≤ tau := by simpa [Metric.mem_closedBall] using hp_ball
    have hxq : dist x q ≤ dist x p + dist p q := dist_triangle x p q
    have h : dist x q ≤ 3 * tau := by linarith
    simpa [Metric.mem_closedBall] using h
  have h2 : A ∩ Metric.closedBall p tau ⊆ A ∩ Metric.closedBall q (3 * tau) :=
    Set.inter_subset_inter_right _ h1
  have h3 : volume (A ∩ Metric.closedBall p tau) ≤
      volume (A ∩ Metric.closedBall q (3 * tau)) :=
    MeasureTheory.measure_mono h2
  exact le_trans hV h3

end Kakeya.Assouad
