import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Intersection volume bound for two δ-tubes at angle θ

Proves that the intersection volume of two δ-tubes whose supporting lines
intersect at angle θ is at most `16δ³/sin θ`.

## Main results

- `projection_bound_angled_lines`: discriminant bound for parallel component
- `orthogonal_projection_le`: perpendicular component ≤ full vector
- `distance_to_line_bound`: cthickening → perpendicular distance ≤ δ
- `cylinder_box_volume_bound`: cylinder volume ≤ 8δ²R via reflection isometry
- `coplanar_xy_lines_intersect`: two non-parallel x-y plane lines intersect
- `coplanar_tube_intersection_volume_bound`: main bound with line-intersect hypothesis
- `angled_tubes_intersection_bound`: bridge lemma for x-y plane tubes
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Streamlined.GeometricLemmas

/-! ### Helper: inner product equals component sum -/

lemma inner_eq_sum (u v : Point3) : inner ℝ u v = ∑ i : Fin 3, u i * v i := by
  rw [PiLp.inner_apply]
  congr with i
  simp <;> ring

/-! ### Projection bound for lines through origin -/

lemma projection_bound_angled_lines
    {δ θ : ℝ} (hδ : 0 < δ) (hθ1 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    {u v x : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hcos : inner ℝ u v = Real.cos θ)
    (h1 : ‖x - (inner ℝ x u) • u‖ ≤ δ)
    (h2 : ‖x - (inner ℝ x v) • v‖ ≤ δ) :
    |inner ℝ x u| ≤ 2 * δ / Real.sin θ := by
  set a : ℝ := inner ℝ x u with ha_def
  set b : ℝ := inner ℝ x v with hb_def
  set c : ℝ := inner ℝ u v with hc_def
  have hc_eq : c = Real.cos θ := hcos
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [Real.pi_pos])
  have h1' : ‖(a • u) - (b • v)‖ ≤ 2 * δ := by
    have h_eq : (a • u) - (b • v) = ((a • u) - x) + (x - (b • v)) := by abel
    rw [h_eq]
    calc ‖((a • u) - x) + (x - (b • v))‖
      ≤ ‖(a • u) - x‖ + ‖x - (b • v)‖ := norm_add_le _ _
    _ = ‖x - (a • u)‖ + ‖x - (b • v)‖ := by rw [norm_sub_rev]
    _ ≤ δ + δ := by gcongr
    _ = 2 * δ := by ring
  set z : Point3 := (a • u) - (b • v) with hz
  have h_norm_sq : ‖z‖ ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b * c := by
    have h3 : ‖z‖ ^ 2 = ‖(a • u)‖ ^ 2 - 2 * inner ℝ (a • u) (b • v) + ‖(b • v)‖ ^ 2 :=
      norm_sub_sq_real (a • u) (b • v)
    rw [h3]
    have h4 : ‖(a • u)‖ ^ 2 = a ^ 2 := by
      have h41 : ‖(a • u)‖ = |a| * ‖u‖ := by simpa [norm_smul] using rfl
      rw [h41, hu]
      have h42 : |a| * 1 = |a| := by ring
      rw [h42]
      have h43 : |a| ^ 2 = a ^ 2 := by rw [sq_abs]
      rw [h43]
    have h5 : ‖(b • v)‖ ^ 2 = b ^ 2 := by
      have h51 : ‖(b • v)‖ = |b| * ‖v‖ := by simpa [norm_smul] using rfl
      rw [h51, hv]
      have h52 : |b| * 1 = |b| := by ring
      rw [h52]
      have h53 : |b| ^ 2 = b ^ 2 := by rw [sq_abs]
      rw [h53]
    have h6 : inner ℝ (a • u) (b • v) = a * b * c := by
      simp [inner_smul_left, inner_smul_right, hc_def] <;> ring
    rw [h4, h5, h6] <;> ring
  have h_ineq : a ^ 2 + b ^ 2 - 2 * a * b * c ≤ (2 * δ) ^ 2 := by
    have h9 : ‖z‖ ^ 2 ≤ (2 * δ) ^ 2 := by gcongr
    rw [h_norm_sq] at h9
    exact h9
  have h_discriminant : a ^ 2 * (1 - c ^ 2) ≤ 4 * δ ^ 2 := by
    nlinarith [sq_nonneg (b - a * c)]
  have h_sin2 : 1 - c ^ 2 = Real.sin θ ^ 2 := by
    rw [show c = Real.cos θ from hcos]
    have h : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    linarith
  have h_main : a ^ 2 * Real.sin θ ^ 2 ≤ 4 * δ ^ 2 := by
    rw [←h_sin2]
    exact h_discriminant
  have h_final : a ^ 2 ≤ (2 * δ / Real.sin θ) ^ 2 := by
    have h_pos : 0 < Real.sin θ := hsin_pos
    have h_goal : (2 * δ / Real.sin θ) ^ 2 = 4 * δ ^ 2 / Real.sin θ ^ 2 := by
      field_simp [h_pos.ne'] <;> ring
    rw [h_goal]
    have h_pos2 : 0 < Real.sin θ ^ 2 := by positivity
    have h_eq2 : a ^ 2 = (a ^ 2 * Real.sin θ ^ 2) / Real.sin θ ^ 2 := by
      field_simp [h_pos2.ne'] <;> ring
    rw [h_eq2]
    gcongr
  have h_abs : |a| ≤ 2 * δ / Real.sin θ := by
    have h_pos : 0 ≤ 2 * δ / Real.sin θ := by positivity
    have h_abs2 : |a| ^ 2 = a ^ 2 := by rw [sq_abs]
    have h_abs3 : |2 * δ / Real.sin θ| ^ 2 = (2 * δ / Real.sin θ) ^ 2 := by rw [sq_abs]
    have h : |a| ^ 2 ≤ |2 * δ / Real.sin θ| ^ 2 := by
      rw [h_abs2, h_abs3]; exact h_final
    have h3 : |a| ≤ |2 * δ / Real.sin θ| := by
      nlinarith [abs_nonneg a, abs_nonneg (2 * δ / Real.sin θ)]
    rw [abs_of_nonneg h_pos] at h3
    exact h3
  exact h_abs

/-! ### Orthogonal projection norm inequality -/

lemma orthogonal_projection_le {u z : Point3} (hu : ‖u‖ = 1) :
    ‖z - (inner ℝ z u) • u‖ ≤ ‖z‖ := by
  let p : Point3 := (inner ℝ z u) • u
  let b : Point3 := z - p
  have h_inn : inner ℝ u u = (1 : ℝ) := by
    have h : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
    rw [h, hu] <;> norm_num
  have h_comm : inner ℝ u z = inner ℝ z u := by
    exact (real_inner_comm u z).symm
  have h_perp : inner ℝ p b = 0 := by
    have h1 : inner ℝ p b = (inner ℝ z u) * inner ℝ u b := by
      dsimp only [p]
      simpa [inner_smul_left] using rfl
    rw [h1]
    have h3 : inner ℝ u b = inner ℝ u z - (inner ℝ z u) * inner ℝ u u := by
      dsimp only [b, p]
      have h4 : inner ℝ u (z - p) = inner ℝ u z - inner ℝ u p := by
        rw [inner_sub_right]
      rw [h4]
      have h5 : inner ℝ u p = (inner ℝ z u) * inner ℝ u u := by
        dsimp only [p]
        rw [inner_smul_right] <;> ring
      rw [h5] <;> ring
    rw [h3, h_inn]
    have h6 : inner ℝ u z = inner ℝ z u := h_comm
    rw [h6] <;> ring
  have h_pyth : ‖p + b‖ ^ 2 = ‖p‖ ^ 2 + ‖b‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real h_perp
    simpa [pow_two] using h
  have h_z : p + b = z := by simp [p, b] <;> abel
  rw [h_z] at h_pyth
  have h4 : ‖b‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h_pyth]
    have h5 : 0 ≤ ‖p‖ ^ 2 := by positivity
    linarith
  have h5 : 0 ≤ ‖b‖ := by positivity
  have h6 : 0 ≤ ‖z‖ := by positivity
  nlinarith

/-! ### Distance to line bound -/

lemma distance_to_line_bound {δ : ℝ} (hδ : 0 ≤ δ) {x q u : Point3} (hu : ‖u‖ = 1)
    {S : Set Point3} (hS : IsCompact S) (hne : S.Nonempty)
    (hS_sub : S ⊆ {q + t • u | t : ℝ})
    (hx : x ∈ Metric.cthickening δ S) :
    ‖(x - q) - (inner ℝ (x - q) u) • u‖ ≤ δ := by
  have h_edist : infEDist x S ≤ ENNReal.ofReal δ := hx
  have h_top : infEDist x S ≠ ⊤ := Metric.infEDist_ne_top hne
  have h_inf : infDist x S ≤ δ := by
    have h : infDist x S = ENNReal.toReal (infEDist x S) := by rfl
    rw [h]
    have h_ofReal_ne_top : ENNReal.ofReal δ ≠ ⊤ := by simp
    have h2 : ENNReal.toReal (infEDist x S) ≤ ENNReal.toReal (ENNReal.ofReal δ) :=
      ENNReal.toReal_mono h_ofReal_ne_top h_edist
    have h3 : ENNReal.toReal (ENNReal.ofReal δ) = δ := ENNReal.toReal_ofReal hδ
    rw [h3] at h2
    exact h2
  obtain ⟨y, hy, h_eqdist⟩ := hS.exists_infDist_eq_dist hne x
  have hdist : dist x y ≤ δ := by rw [←h_eqdist]; exact h_inf
  rcases hS_sub hy with ⟨t, hyt⟩
  have h_y_eq : y = q + t • u := hyt.symm
  have h2 : y - q = t • u := by rw [h_y_eq] <;> simp
  set w : Point3 := x - y with hw_def
  set a : ℝ := inner ℝ w u with ha_def
  have h_inn2 : inner ℝ u u = 1 := by
    have h : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
    rw [h, hu] <;> norm_num
  have h_perp : ‖w - a • u‖ ≤ ‖w‖ := orthogonal_projection_le hu
  have h_eq1 : x - q = w + (y - q) := by
    simp [hw_def] <;> abel
  have h6 : x - q = w + t • u := by
    rw [h_eq1, h2]
  have h_inner : inner ℝ (x - q) u = a + t := by
    rw [h6]
    have h : inner ℝ (w + t • u) u = inner ℝ w u + t * inner ℝ u u := by
      simpa [inner_add_left, inner_smul_left] using rfl
    rw [h, ha_def, h_inn2] <;> ring
  have h_main : (x - q) - inner ℝ (x - q) u • u = w - a • u := by
    have h7 : (x - q) - inner ℝ (x - q) u • u = (w + t • u) - (a + t) • u := by
      rw [h_inner, h6]
    rw [h7]
    have h8 : (w + t • u) - (a + t) • u = w - a • u := by
      rw [add_smul] <;> abel
    exact h8
  rw [h_main]
  have h4 : ‖w‖ = ‖x - y‖ := by rfl
  rw [h4] at h_perp
  have h5 : ‖x - y‖ = dist x y := by rfl
  rw [h5] at h_perp
  exact le_trans h_perp hdist

/-! ### Householder reflection helper -/

/-- Explicit Householder reflection mapping unit vector u to e0. -/
lemma exists_isometry_map_to_e0 (u : Point3) (hu : ‖u‖ = 1) :
    ∃ (L : Point3 ≃ₗᵢ[ℝ] Point3), L u = EuclideanSpace.single 0 1 := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  have he0 : ‖e0‖ = 1 := by
    simp [e0, EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;> norm_num
  by_cases h : u = e0
  · refine' ⟨LinearIsometryEquiv.refl ℝ Point3, _⟩
    have h_goal : (LinearIsometryEquiv.refl ℝ Point3) u = e0 := by
      rw [h] <;> rfl
    exact h_goal
  · let v : Point3 := u - e0
    have hv_ne_zero : v ≠ 0 := by
      intro h2
      have h3 : u = e0 := sub_eq_zero.mp h2
      exact h h3
    have h_v_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne_zero
    have h_v2_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos h_v_pos
    have h_v2_ne_zero : ‖v‖ ^ 2 ≠ 0 := h_v2_pos.ne'
    let coeff : Point3 → ℝ := fun x => 2 * inner ℝ x v / ‖v‖ ^ 2
    let H : Point3 → Point3 := fun x => x - (coeff x) • v
    have H_add : ∀ (x y : Point3), H (x + y) = H x + H y := by
      intro x y
      have h1 : coeff (x + y) = coeff x + coeff y := by
        simp only [coeff]
        rw [inner_add_left] <;> ring
      simp only [H, h1]
      rw [add_smul, sub_add] <;> abel
    have H_smul : ∀ (a : ℝ) (x : Point3), H (a • x) = a • H x := by
      intro a x
      have h1 : coeff (a • x) = a * coeff x := by
        simp only [coeff]
        have h2 : inner ℝ (a • x) v = a * inner ℝ x v := by
          rw [inner_smul_left] <;> simp
        rw [h2] <;> ring
      simp only [H, h1]
      have h3 : a • (x - coeff x • v) = a • x - (a * coeff x) • v := by
        have h4 : a • (x - coeff x • v) = a • x - a • (coeff x • v) := by
          exact smul_sub a x (coeff x • v)
        rw [h4]
        have h5 : a • (coeff x • v) = (a * coeff x) • v :=
          smul_smul a (coeff x) v
        rw [h5] <;> rfl
      exact h3.symm
    let Hlin : Point3 →ₗ[ℝ] Point3 :=
      { toFun := H
        map_add' := H_add
        map_smul' := H_smul }
    have H_inner : ∀ (x y : Point3), inner ℝ (H x) (H y) = inner ℝ x y := by
      intro x y
      simp only [H]
      set cx := coeff x with hcx
      set cy := coeff y with hcy
      have h_expand : inner ℝ (x - cx • v) (y - cy • v) =
          inner ℝ x y - cx * inner ℝ v y - cy * inner ℝ x v + cx * cy * inner ℝ v v := by
        calc
          inner ℝ (x - cx • v) (y - cy • v)
            = inner ℝ x (y - cy • v) - inner ℝ (cx • v) (y - cy • v) := by
              rw [inner_sub_left]
          _ = inner ℝ x y - inner ℝ x (cy • v) - (inner ℝ (cx • v) y - inner ℝ (cx • v) (cy • v)) := by
              rw [inner_sub_right, inner_sub_right]
          _ = inner ℝ x y - cy * inner ℝ x v - (cx * inner ℝ v y - cx * cy * inner ℝ v v) := by
              have h1 : inner ℝ x (cy • v) = cy * inner ℝ x v := by
                rw [inner_smul_right] <;> simp
              have h2 : inner ℝ (cx • v) y = cx * inner ℝ v y := by
                rw [inner_smul_left] <;> simp
              have h3 : inner ℝ (cx • v) (cy • v) = cx * cy * inner ℝ v v := by
                rw [inner_smul_left, inner_smul_right] <;> simp <;> ring
              rw [h1, h2, h3]
          _ = inner ℝ x y - cx * inner ℝ v y - cy * inner ℝ x v + cx * cy * inner ℝ v v := by ring
      rw [h_expand]
      have h_vv : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      have h_comm : inner ℝ v y = inner ℝ y v := (real_inner_comm v y).symm
      rw [h_vv, h_comm]
      simp only [coeff, hcx, hcy]
      field_simp [h_v2_ne_zero] <;> ring
    have H_norm : ∀ (x : Point3), ‖H x‖ = ‖x‖ := by
      intro x
      have h1 : ‖H x‖ ^ 2 = ‖x‖ ^ 2 := by
        have h2 : inner ℝ (H x) (H x) = inner ℝ x x := H_inner x x
        have h3 : ‖H x‖ ^ 2 = inner ℝ (H x) (H x) :=
          (real_inner_self_eq_norm_sq (H x)).symm
        have h4 : ‖x‖ ^ 2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
        rw [h3, h2, ←h4]
      have h5 : 0 ≤ ‖H x‖ := by positivity
      have h6 : 0 ≤ ‖x‖ := by positivity
      nlinarith
    have H_invol : ∀ (x : Point3), H (H x) = x := by
      intro x
      set a := inner ℝ x v with ha
      have h1 : inner ℝ (H x) v = -a := by
        simp only [H]
        set cx := coeff x with hcx
        have h_expand : inner ℝ (x - cx • v) v = inner ℝ x v - cx * inner ℝ v v := by
          have h1 : inner ℝ (x - cx • v) v = inner ℝ x v - inner ℝ (cx • v) v := by
            rw [inner_sub_left]
          rw [h1]
          have h2 : inner ℝ (cx • v) v = cx * inner ℝ v v := by
            rw [inner_smul_left] <;> simp
          rw [h2] <;> ring
        rw [h_expand]
        have h_vv : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
        rw [h_vv]
        simp only [coeff, hcx, ha]
        field_simp [h_v2_ne_zero] <;> ring
      have h_coeff_H : coeff (H x) = -coeff x := by
        simp only [coeff, h1] <;> ring
      simp only [H, h_coeff_H]
      rw [neg_smul, sub_neg_eq_add] <;> abel
    let Hli : Point3 ≃ₗᵢ[ℝ] Point3 :=
      { Hlin with
        invFun := H
        left_inv := H_invol
        right_inv := H_invol
        norm_map' := H_norm }
    have H_u : H u = e0 := by
      have h4 : inner ℝ u v = ‖v‖ ^ 2 / 2 := by
        have h5 : inner ℝ u v = inner ℝ u u - inner ℝ u e0 := by
          simp [v, inner_sub_right] <;> ring
        have h6 : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
        have h9 : ‖v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u e0 + ‖e0‖ ^ 2 := by
          have h10 : ‖u - e0‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u e0 + ‖e0‖ ^ 2 := by
            rw [norm_sub_sq_real] <;> ring
          simpa [v] using h10
        rw [h5, h6, h9, hu, he0] <;> ring
      have h_cu : coeff u = 1 := by
        simp only [coeff, h4]
        field_simp [h_v2_ne_zero] <;> ring
      simp only [H, h_cu]
      have h10 : u - (1 : ℝ) • v = e0 := by
        simp [v, one_smul] <;> abel
      exact h10
    exact ⟨Hli, H_u⟩

/-! ### Cylinder box volume bound -/

lemma cylinder_box_volume_bound (u : Point3) (hu : ‖u‖ = 1)
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) :
    MeasureTheory.volume {y : Point3 |
      ‖y - (inner ℝ y u) • u‖ ≤ δ ∧ |inner ℝ y u| ≤ R} ≤
      ENNReal.ofReal (8 * δ ^ 2 * R) := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  rcases exists_isometry_map_to_e0 u hu with ⟨L, hL⟩
  let S := {y : Point3 | ‖y - (inner ℝ y u) • u‖ ≤ δ ∧ |inner ℝ y u| ≤ R}
  have h_inner_pres : ∀ (a b : Point3), inner ℝ (L a) (L b) = inner ℝ a b :=
    fun a b => L.toLinearIsometry.inner_map_map a b
  have h_cont2 : Continuous (fun y : Point3 => inner ℝ y u) := by
    have h_pair : Continuous (fun y : Point3 => (y, u)) := Continuous.prodMk_left u
    exact continuous_inner.comp h_pair
  have h_smul : Continuous (fun y : Point3 => (inner ℝ y u) • u) :=
    h_cont2.smul continuous_const
  have h_cont1 : Continuous (fun y : Point3 => ‖y - (inner ℝ y u) • u‖) :=
    (continuous_id.sub h_smul).norm
  have hS_meas : MeasurableSet S := by
    have hP : MeasurableSet {y : Point3 | ‖y - (inner ℝ y u) • u‖ ≤ δ} := by
      apply IsClosed.measurableSet
      exact isClosed_le h_cont1 continuous_const
    have hQ : MeasurableSet {y : Point3 | |inner ℝ y u| ≤ R} := by
      apply IsClosed.measurableSet
      exact isClosed_le h_cont2.abs continuous_const
    exact hP.inter hQ
  have hmp_symm : MeasurePreserving L.symm MeasureTheory.volume MeasureTheory.volume :=
    LinearIsometryEquiv.measurePreserving L.symm
  have h_vol : MeasureTheory.volume (L '' S) = MeasureTheory.volume S := by
    have h_eq : (L.symm) ⁻¹' S = L '' S := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        refine ⟨L.symm x, hx, ?_⟩
        exact L.apply_symm_apply x
      · rintro ⟨y, hy, rfl⟩
        rw [L.symm_apply_apply]
        exact hy
    have hS_null : NullMeasurableSet S volume := hS_meas.nullMeasurableSet
    rw [←h_eq]
    exact hmp_symm.measure_preimage hS_null
  have h_image_subset : L '' S ⊆ axisBox (2 * R) (2 * δ) (2 * δ) := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    have h1 : ‖y - (inner ℝ y u) • u‖ ≤ δ := hy.1
    have h2 : |inner ℝ y u| ≤ R := hy.2
    set a : ℝ := inner ℝ y u with ha
    set v : Point3 := L y with hv
    have h3 : inner ℝ v e0 = a := by
      have h4 : inner ℝ (L y) (L u) = inner ℝ y u := h_inner_pres y u
      rw [hL] at h4
      exact h4
    have h5 : v - a • e0 = L (y - a • u) := by
      have h6 : L (y - a • u) = L y - L (a • u) := L.map_sub y (a • u)
      rw [h6]
      have h7 : L (a • u) = a • L u := L.map_smul a u
      rw [h7, hL] <;> rfl
    have h8 : ‖v - a • e0‖ ≤ δ := by
      rw [h5]
      have h9 : ‖L (y - a • u)‖ = ‖y - a • u‖ := L.norm_map _
      rw [h9]; exact h1
    have h_v0 : v 0 = a := by
      have h18 : v 0 = inner ℝ v e0 := by
        simp [e0, EuclideanSpace.single_apply, inner_eq_sum, Fin.sum_univ_succ] <;> ring
      rw [h18, h3]
    have h10 : (v - a • e0) 0 = 0 := by
      have h : (v - a • e0) 0 = v 0 - a := by
        simp [e0, EuclideanSpace.single_apply] <;> ring
      rw [h, h_v0] <;> ring
    have h11 : (v - a • e0) 1 = v 1 := by
      simp [e0, EuclideanSpace.single_apply] <;> ring
    have h12 : (v - a • e0) 2 = v 2 := by
      simp [e0, EuclideanSpace.single_apply] <;> ring
    have h13 : ‖v - a • e0‖ ^ 2 = (v 1)^2 + (v 2)^2 := by
      have h14 : ‖v - a • e0‖ ^ 2 = inner ℝ (v - a • e0) (v - a • e0) :=
        (real_inner_self_eq_norm_sq (v - a • e0)).symm
      rw [h14]
      have h15 : inner ℝ (v - a • e0) (v - a • e0) = ∑ i : Fin 3, ((v - a • e0) i)^2 := by
        rw [inner_eq_sum]
        congr with i <;> ring
      rw [h15]
      have h_sum : ∑ i : Fin 3, ((v - a • e0) i)^2 =
          ((v - a • e0) 0)^2 + ((v - a • e0) 1)^2 + ((v - a • e0) 2)^2 := by
        simp [Fin.sum_univ_succ]
        <;> ring
      rw [h_sum, h10, h11, h12] <;> ring
    have h16 : (v 1)^2 + (v 2)^2 ≤ δ^2 := by
      have h17 : ‖v - a • e0‖ ^ 2 ≤ δ^2 := by
        have h18 : ‖v - a • e0‖ ≤ δ := h8
        have h19 : 0 ≤ ‖v - a • e0‖ := by positivity
        have h20 : 0 ≤ δ := by positivity
        exact sq_le_sq.mpr (by simpa [abs_of_nonneg h19, abs_of_nonneg h20] using h18)
      rw [h13] at h17
      exact h17
    have h17 : |v 0| ≤ R := by
      rw [h_v0]; exact h2
    have h20 : |v 1| ≤ δ := by
      have h22 : (v 1)^2 ≤ δ^2 := by linarith [h16, sq_nonneg (v 2)]
      have h23 : |v 1| ≤ |δ| := sq_le_sq.mp h22
      rw [abs_of_pos hδ] at h23
      exact h23
    have h21 : |v 2| ≤ δ := by
      have h22 : (v 2)^2 ≤ δ^2 := by linarith [h16, sq_nonneg (v 1)]
      have h23 : |v 2| ≤ |δ| := sq_le_sq.mp h22
      rw [abs_of_pos hδ] at h23
      exact h23
    simpa [axisBox] using ⟨h17, h20, h21⟩
  have h_box : MeasureTheory.volume (axisBox (2 * R) (2 * δ) (2 * δ)) =
      ENNReal.ofReal ((2 * R) * (2 * δ) * (2 * δ)) :=
    volume_axisBox (2 * R) (2 * δ) (2 * δ) (by positivity) (by positivity) (by positivity)
  have h_mul : (2 * R) * (2 * δ) * (2 * δ) = 8 * δ ^ 2 * R := by ring
  have h_mono : MeasureTheory.volume (L '' S) ≤ MeasureTheory.volume (axisBox (2 * R) (2 * δ) (2 * δ)) :=
    (measure_mono h_image_subset : MeasureTheory.volume (L '' S) ≤ _)
  have h_main : MeasureTheory.volume (L '' S) ≤ ENNReal.ofReal (8 * δ ^ 2 * R) := by
    calc MeasureTheory.volume (L '' S)
      ≤ MeasureTheory.volume (axisBox (2 * R) (2 * δ) (2 * δ)) := h_mono
    _ = ENNReal.ofReal ((2 * R) * (2 * δ) * (2 * δ)) := h_box
    _ = ENNReal.ofReal (8 * δ ^ 2 * R) := by rw [h_mul]
  rw [←h_vol]
  exact h_main

/-! ### Coplanar x-y plane lines intersect -/

lemma coplanar_xy_lines_intersect
    {u v p1 p2 : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hTz : u 2 = 0) (hUz : v 2 = 0)
    (h_same_z : p1 2 = p2 2)
    {θ : ℝ} (hθ1 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    (hcos : inner ℝ u v = Real.cos θ) :
    ∃ (q : Point3), q ∈ {p1 + t • u | t : ℝ} ∧ q ∈ {p2 + s • v | s : ℝ} := by
  let a : ℝ := u 0
  let b : ℝ := u 1
  let c : ℝ := v 0
  let d : ℝ := v 1
  let dx : ℝ := (p2 - p1) 0
  let dy : ℝ := (p2 - p1) 1
  let det : ℝ := a * d - b * c
  have h_norm2_u : ‖u‖ ^ 2 = (u 0)^2 + (u 1)^2 + (u 2)^2 := by
    have h : ‖u‖ ^ 2 = inner ℝ u u := by
      exact (real_inner_self_eq_norm_sq u).symm
    rw [h]
    have h2 : inner ℝ u u = ∑ i : Fin 3, u i * u i := inner_eq_sum u u
    rw [h2]
    simp [Fin.sum_univ_succ] <;> ring
  have h_u2 : a^2 + b^2 = 1 := by
    have h1 : ‖u‖ ^ 2 = a^2 + b^2 + (u 2)^2 := by
      simpa [h_norm2_u, a, b] using rfl
    have h2 : ‖u‖ ^ 2 = 1 := by rw [hu] <;> norm_num
    rw [h2] at h1
    rw [hTz] at h1
    <;> linarith
  have h_norm2_v : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 + (v 2)^2 := by
    have h : ‖v‖ ^ 2 = inner ℝ v v := by
      exact (real_inner_self_eq_norm_sq v).symm
    rw [h]
    have h2 : inner ℝ v v = ∑ i : Fin 3, v i * v i := inner_eq_sum v v
    rw [h2]
    simp [Fin.sum_univ_succ] <;> ring
  have h_v2 : c^2 + d^2 = 1 := by
    have h1 : ‖v‖ ^ 2 = c^2 + d^2 + (v 2)^2 := by
      simpa [h_norm2_v, c, d] using rfl
    have h2 : ‖v‖ ^ 2 = 1 := by rw [hv] <;> norm_num
    rw [h2] at h1
    rw [hUz] at h1
    <;> linarith
  have h_inner_sum : inner ℝ u v = a * c + b * d := by
    have h : inner ℝ u v = ∑ i : Fin 3, u i * v i := inner_eq_sum u v
    rw [h]
    simp [Fin.sum_univ_succ, hTz, hUz, a, b, c, d] <;> ring
  have h_inner : a * c + b * d = Real.cos θ := by
    rw [h_inner_sum] at hcos
    exact hcos
  have h_det2 : det^2 = Real.sin θ^2 := by
    have h : det^2 + (a * c + b * d)^2 = (a^2 + b^2) * (c^2 + d^2) := by
      simp [det] <;> ring
    rw [h_u2, h_v2] at h
    rw [h_inner] at h
    have h2 : Real.sin θ^2 + Real.cos θ^2 = 1 := Real.sin_sq_add_cos_sq θ
    linarith
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [Real.pi_pos])
  have h_det_ne_zero : det ≠ 0 := by
    intro h_eq
    rw [h_eq] at h_det2
    have h' : Real.sin θ ^ 2 = 0 := by linarith
    have h'' : Real.sin θ = 0 := by nlinarith
    exact hsin_pos.ne h''.symm
  let t : ℝ := (dx * d - c * dy) / det
  let s : ℝ := (b * dx - a * dy) / det
  let q : Point3 := p1 + t • u
  have h_q1 : q ∈ {p1 + t • u | t : ℝ} := ⟨t, rfl⟩
  have h_q2 : q ∈ {p2 + s • v | s : ℝ} := by
    refine ⟨s, ?_⟩
    have h_eq : p2 + s • v = q := by
      ext i
      fin_cases i
      · simp [q, t, s, a, b, c, d, dx, dy, h_det_ne_zero] <;> field_simp [h_det_ne_zero] <;> ring
      · simp [q, t, s, a, b, c, d, dx, dy, h_det_ne_zero] <;> field_simp [h_det_ne_zero] <;> ring
      · simp [q, t, s, hTz, hUz, h_same_z] <;> abel
    exact h_eq
  exact ⟨q, h_q1, h_q2⟩

/-! ### Main intersection volume bound -/

lemma coplanar_tube_intersection_volume_bound
    {δ θ : ℝ} (hδ : 0 < δ) (hθ1 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    {T1 T2 : DeltaTube δ}
    (hcos : inner ℝ T1.direction T2.direction = Real.cos θ)
    (h_lines_intersect : ∃ (q : Point3),
        q ∈ {T1.base + t • T1.direction | t : ℝ} ∧
        q ∈ {T2.base + s • T2.direction | s : ℝ}) :
    MeasureTheory.volume (T1.carrier ∩ T2.carrier) ≤
      ENNReal.ofReal (16 * δ ^ 3 / Real.sin θ) := by
  rcases h_lines_intersect with ⟨q, hq1, hq2⟩
  have hu : ‖T1.direction‖ = 1 := T1.direction_unit
  have hv : ‖T2.direction‖ = 1 := T2.direction_unit
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [Real.pi_pos])
  set R : ℝ := 2 * δ / Real.sin θ with hR
  have hR_pos : 0 < R := by positivity
  let u := T1.direction
  let v := T2.direction
  let S1 := unitSegment T1.base T1.direction
  let S2 := unitSegment T2.base T2.direction
  have hS1_compact : IsCompact S1 := by
    apply IsCompact.image (isCompact_Icc)
    continuity
  have hS2_compact : IsCompact S2 := by
    apply IsCompact.image (isCompact_Icc)
    continuity
  have hS1_nonempty : S1.Nonempty := ⟨T1.base, 0, by norm_num, by simp⟩
  have hS2_nonempty : S2.Nonempty := ⟨T2.base, 0, by norm_num, by simp⟩
  rcases hq1 with ⟨t0, hq1_eq⟩
  rcases hq2 with ⟨s0, hq2_eq⟩
  have hS1_line : S1 ⊆ {q + t • u | t : ℝ} := by
    intro x hx
    rcases hx with ⟨t, _, rfl⟩
    refine ⟨t - t0, ?_⟩
    have hq : q = T1.base + t0 • u := hq1_eq.symm
    have h : T1.base + t • u = q + (t - t0) • u := by
      rw [hq] <;> simp [add_smul, sub_smul] <;> abel
    exact h.symm
  have hS2_line : S2 ⊆ {q + s • v | s : ℝ} := by
    intro x hx
    rcases hx with ⟨s, _, rfl⟩
    refine ⟨s - s0, ?_⟩
    have hq : q = T2.base + s0 • v := hq2_eq.symm
    have h : T2.base + s • v = q + (s - s0) • v := by
      rw [hq] <;> simp [add_smul, sub_smul] <;> abel
    exact h.symm
  have h_main : T1.carrier ∩ T2.carrier ⊆
      {x : Point3 | ‖(x - q) - (inner ℝ (x - q) u) • u‖ ≤ δ ∧
          |inner ℝ (x - q) u| ≤ R} := by
    intro x hx
    set y : Point3 := x - q with hy_def
    have h_dist1 : ‖y - (inner ℝ y u) • u‖ ≤ δ :=
      distance_to_line_bound (by linarith) hu hS1_compact hS1_nonempty hS1_line hx.1
    have h_dist2 : ‖y - (inner ℝ y v) • v‖ ≤ δ :=
      distance_to_line_bound (by linarith) hv hS2_compact hS2_nonempty hS2_line hx.2
    have h_proj : |inner ℝ y u| ≤ R :=
      projection_bound_angled_lines hδ hθ1 hθ2 hu hv hcos h_dist1 h_dist2
    exact ⟨h_dist1, h_proj⟩
  have h_meas : MeasurableSet (T1.carrier ∩ T2.carrier) := by
    apply MeasurableSet.inter
    · exact IsClosed.measurableSet (isClosed_Iic.preimage continuous_infEDist)
    · exact IsClosed.measurableSet (isClosed_Iic.preimage continuous_infEDist)
  let trans : Point3 ≃ᵢ Point3 :=
    { toFun := fun x => x - q
      invFun := fun x => x + q
      left_inv := by intro x; simp [add_sub_cancel]
      right_inv := by intro x; simp [sub_add_cancel]
      isometry_toFun := by
        intro x y
        have h : (x - q) - (y - q) = x - y := by abel
        simpa [dist_eq_norm, h] using rfl }
  have h_translate : MeasureTheory.volume (trans '' (T1.carrier ∩ T2.carrier)) =
      MeasureTheory.volume (T1.carrier ∩ T2.carrier) := by
    have hmp_symm : MeasurePreserving trans.symm volume volume :=
      measurePreserving_add_right volume q
    have h_eq : trans.symm ⁻¹' (T1.carrier ∩ T2.carrier) = trans '' (T1.carrier ∩ T2.carrier) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx
        refine ⟨trans.symm x, hx, ?_⟩
        exact trans.apply_symm_apply x
      · rintro ⟨y, hy, rfl⟩
        rw [trans.symm_apply_apply]
        exact hy
    rw [←h_eq]
    exact hmp_symm.measure_preimage h_meas.nullMeasurableSet
  rw [←h_translate]
  have h_image_subset : trans '' (T1.carrier ∩ T2.carrier) ⊆
      {y : Point3 | ‖y - (inner ℝ y u) • u‖ ≤ δ ∧ |inner ℝ y u| ≤ R} := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have h : x ∈ T1.carrier ∩ T2.carrier := hx
    have h' := h_main h
    simpa [trans] using h'
  have h_cyl := cylinder_box_volume_bound u hu δ R hδ hR_pos
  calc MeasureTheory.volume (trans '' (T1.carrier ∩ T2.carrier))
    ≤ MeasureTheory.volume {y : Point3 | ‖y - (inner ℝ y u) • u‖ ≤ δ ∧ |inner ℝ y u| ≤ R} :=
      measure_mono h_image_subset
  _ ≤ ENNReal.ofReal (8 * δ ^ 2 * R) := h_cyl
  _ = ENNReal.ofReal (16 * δ ^ 3 / Real.sin θ) := by
    have h_eq : 8 * δ ^ 2 * R = 16 * δ ^ 3 / Real.sin θ := by
      rw [hR]
      field_simp [hsin_pos.ne'] <;> ring
    rw [h_eq]

/-- Intersection volume bound for two δ-tubes in the x-y plane at angle θ.

Directions must have z-component 0, and bases must have the same z-coordinate. -/
lemma angled_tubes_intersection_bound
    {δ θ : ℝ} (hδ : 0 < δ) (hθ1 : 0 < θ) (hθ2 : θ ≤ Real.pi / 2)
    (T U : DeltaTube δ)
    (hTz : T.direction 2 = 0) (hUz : U.direction 2 = 0)
    (h_same_z : T.base 2 = U.base 2)
    (h_angle : Real.cos θ = inner ℝ T.direction U.direction) :
    MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
      ENNReal.ofReal (16 * δ^3 / Real.sin θ) := by
  have hcos : inner ℝ T.direction U.direction = Real.cos θ := h_angle.symm
  have h_lines_intersect : ∃ (q : Point3),
      q ∈ {T.base + t • T.direction | t : ℝ} ∧
      q ∈ {U.base + s • U.direction | s : ℝ} :=
    coplanar_xy_lines_intersect T.direction_unit U.direction_unit hTz hUz h_same_z hθ1 hθ2 hcos
  exact coplanar_tube_intersection_volume_bound hδ hθ1 hθ2 hcos h_lines_intersect

end GeometricLemmas

end Kakeya.Streamlined
