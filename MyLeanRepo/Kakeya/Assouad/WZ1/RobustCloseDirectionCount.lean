import MyLeanRepo.Kakeya.Assouad.FrostmanConvexWolff
import MyLeanRepo.Kakeya.Assouad.TubeBaseAlignment
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# WZ1 robust close-direction count

Closed proof of WZ1 Lemma 7: place all active tubes whose directions are close
to one fixed active direction in a common bounded convex cylinder, then use the
Convex-Wolff count to bound their number.
-/

noncomputable section

open Kakeya MeasureTheory Set

namespace Kakeya.Assouad

/-- For unit vectors u, v, the norm of the perpendicular component of v
relative to u equals the norm of their cross product. -/
lemma radial_norm_eq_cross_norm {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖wz1Cross u v‖ = ‖v - inner ℝ u v • u‖ := by
  have h_cross : ‖wz1Cross u v‖ =
      ‖u‖ * ‖v‖ * Real.sin (InnerProductGeometry.angle u v) :=
    InnerProductGeometry.norm_toLp_symm_crossProduct (u : Fin 3 → ℝ) (v : Fin 3 → ℝ)
  have h_inner : Real.cos (InnerProductGeometry.angle u v) = inner ℝ u v := by
    have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u v
    rw [hu, hv] at h
    simpa using h
  have h_cross' : ‖wz1Cross u v‖ = Real.sin (InnerProductGeometry.angle u v) := by
    rw [h_cross, hu, hv]; ring
  have h1 : ‖wz1Cross u v‖ ^ 2 = 1 - (inner ℝ u v) ^ 2 := by
    rw [h_cross']
    have h_sin2 := Real.sin_sq_add_cos_sq (InnerProductGeometry.angle u v)
    rw [h_inner] at h_sin2
    linarith
  have h_inn1 : inner ℝ v (inner ℝ u v • u) = (inner ℝ u v) ^ 2 := by
    have h : inner ℝ v (inner ℝ u v • u) = (inner ℝ u v) * inner ℝ v u := by
      rw [inner_smul_right]
    rw [h]
    have hcomm : inner ℝ v u = inner ℝ u v := (real_inner_comm v u).symm
    rw [hcomm]; ring
  have h_norm : ‖inner ℝ u v • u‖ ^ 2 = (inner ℝ u v) ^ 2 := by
    rw [norm_smul, hu]; simp
  have h2 : ‖v - inner ℝ u v • u‖ ^ 2 = 1 - (inner ℝ u v) ^ 2 := by
    have h_expand := norm_sub_sq_real v (inner ℝ u v • u)
    rw [h_expand, h_inn1, h_norm, hv]; ring
  have h3 : ‖wz1Cross u v‖ ^ 2 = ‖v - inner ℝ u v • u‖ ^ 2 := by
    rw [h1, h2]
  have h4 : 0 ≤ ‖wz1Cross u v‖ := by positivity
  have h5 : 0 ≤ ‖v - inner ℝ u v • u‖ := by positivity
  nlinarith

/-- The perpendicular projection z - inner(z,u)•u is contractive when ‖u‖=1. -/
lemma perp_projection_contractive {u z : Point3} (hu : ‖u‖ = 1) :
    ‖z - inner ℝ z u • u‖ ≤ ‖z‖ := by
  have h_inn1 : inner ℝ z (inner ℝ z u • u) = (inner ℝ z u) ^ 2 := by
    rw [inner_smul_right]; ring
  have h_norm : ‖inner ℝ z u • u‖ ^ 2 = (inner ℝ z u) ^ 2 := by
    rw [norm_smul, hu]; simp
  have h1 : ‖z - inner ℝ z u • u‖ ^ 2 = ‖z‖ ^ 2 - (inner ℝ z u) ^ 2 := by
    rw [norm_sub_sq_real z (inner ℝ z u • u), h_inn1, h_norm]; ring
  have h4 : (inner ℝ z u) ^ 2 ≥ 0 := by positivity
  have h5 : ‖z - inner ℝ z u • u‖ ^ 2 ≤ ‖z‖ ^ 2 := by linarith
  have h6 : 0 ≤ ‖z - inner ℝ z u • u‖ := by positivity
  have h7 : 0 ≤ ‖z‖ := by positivity
  nlinarith

/-- Norm squared of a Point3 equals sum of squared coordinates. -/
lemma point3_norm_sq (w : Point3) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
  have h : ‖w‖ ^ 2 = inner ℝ w w := by rw [← real_inner_self_eq_norm_sq]
  rw [h]
  have h2 : inner ℝ w w = ∑ i : Fin 3, w i ^ 2 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    <;> simp [pow_two] <;> rfl
  rw [h2]
  have h3 : ∑ i : Fin 3, w i ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
    simp [Fin.sum_univ_succ] <;> ring
  exact h3

/-- If |x|^2 ≤ y^2 and y ≥ 0, then |x| ≤ y. -/
lemma abs_le_of_sq_le {x y : ℝ} (hy : 0 ≤ y) (h : |x| ^ 2 ≤ y ^ 2) : |x| ≤ y := by
  have h3 : 0 ≤ |x| := by positivity
  by_contra h4
  have h5 : y < |x| := by linarith
  have h6 : y ^ 2 < |x| ^ 2 := by nlinarith
  linarith

/-- Volume upper bound for an oriented rectangular box. -/
lemma oriented_box_volume_bound
    (A : Point3 ≃ₗᵢ[ℝ] Point3) (p : Point3)
    (d0 d1 d2 : ℝ) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) :
    let W : Set Point3 := {x |
      |(A (x - p)) 0| ≤ d0 / 2 ∧
      |(A (x - p)) 1| ≤ d1 / 2 ∧
      |(A (x - p)) 2| ≤ d2 / 2}
    MeasureTheory.volume W ≤ ENNReal.ofReal (d0 * d1 * d2) := by
  let W : Set Point3 := {x |
    |(A (x - p)) 0| ≤ d0 / 2 ∧
    |(A (x - p)) 1| ≤ d1 / 2 ∧
    |(A (x - p)) 2| ≤ d2 / 2}
  let T : Point3 → Point3 := fun x => A (x - p)
  let T_inv : Point3 → Point3 := fun y => p + A.symm y
  let W' : Set Point3 := T '' W
  let F : Point3 → (Fin 3 → ℝ) := WithLp.ofLp (p := 2)
  let G : (Fin 3 → ℝ) → Point3 := WithLp.toLp (p := 2)
  let W'' : Set (Fin 3 → ℝ) := F '' W'

  have hT_left : ∀ x, T_inv (T x) = x := by
    intro x; simp [T, T_inv] <;> abel
  have hT_right : ∀ y, T (T_inv y) = y := by
    intro y; simp [T, T_inv] <;> abel

  let T_equiv : Point3 ≃ᵐ Point3 :=
    { toFun := T
      invFun := T_inv
      left_inv := hT_left
      right_inv := hT_right
      measurable_toFun := A.continuous.comp (continuous_id.sub continuous_const) |>.measurable
      measurable_invFun := (continuous_const.add A.symm.continuous).measurable }

  have hW'_eq : W' = {y : Point3 |
      |y 0| ≤ d0 / 2 ∧ |y 1| ≤ d1 / 2 ∧ |y 2| ≤ d2 / 2} := by
    ext y
    simp only [W', Set.mem_image, W, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      refine ⟨T_inv y, ?_, ?_⟩
      · simpa [T, T_inv] using hy
      · exact hT_right y

  have hW'_meas : MeasurableSet W' := by
    rw [hW'_eq]
    have hcont0 : Continuous (fun y : Point3 => y 0) := by fun_prop
    have hcont1 : Continuous (fun y : Point3 => y 1) := by fun_prop
    have hcont2 : Continuous (fun y : Point3 => y 2) := by fun_prop
    let s0 : Set Point3 := (fun y : Point3 => y 0) ⁻¹' Set.Icc (-d0 / 2) (d0 / 2)
    let s1 : Set Point3 := (fun y : Point3 => y 1) ⁻¹' Set.Icc (-d1 / 2) (d1 / 2)
    let s2 : Set Point3 := (fun y : Point3 => y 2) ⁻¹' Set.Icc (-d2 / 2) (d2 / 2)
    have hI0 : IsClosed (Set.Icc (-d0 / 2) (d0 / 2) : Set ℝ) := isClosed_Icc
    have hI1 : IsClosed (Set.Icc (-d1 / 2) (d1 / 2) : Set ℝ) := isClosed_Icc
    have hI2 : IsClosed (Set.Icc (-d2 / 2) (d2 / 2) : Set ℝ) := isClosed_Icc
    have hs0 : IsClosed s0 := hI0.preimage hcont0
    have hs1 : IsClosed s1 := hI1.preimage hcont1
    have hs2 : IsClosed s2 := hI2.preimage hcont2
    have h7 : {y : Point3 | |y 0| ≤ d0 / 2 ∧ |y 1| ≤ d1 / 2 ∧ |y 2| ≤ d2 / 2} =
        s0 ∩ (s1 ∩ s2) := by
      ext y
      have h_iff : ∀ (x : ℝ) (b : ℝ), |x| ≤ b ↔ -b ≤ x ∧ x ≤ b := by
        intro x b; exact abs_le
      simp only [s0, s1, s2, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc,
        Set.mem_setOf_eq]
      have h_eq1 :
          (|y 0| ≤ d0 / 2 ∧ |y 1| ≤ d1 / 2 ∧ |y 2| ≤ d2 / 2) ↔
            ((-d0 / 2 ≤ y 0 ∧ y 0 ≤ d0 / 2) ∧
              ((-d1 / 2 ≤ y 1 ∧ y 1 ≤ d1 / 2) ∧
                (-d2 / 2 ≤ y 2 ∧ y 2 ≤ d2 / 2))) := by
        rw [h_iff (y 0) (d0 / 2), h_iff (y 1) (d1 / 2), h_iff (y 2) (d2 / 2)]
        <;> ring_nf <;> constructor <;> intro h <;> tauto
      exact h_eq1
    rw [h7]
    exact hs0.measurableSet.inter (hs1.measurableSet.inter hs2.measurableSet)

  have hW_meas : MeasurableSet W := by
    have h : W = T_equiv ⁻¹' W' := by
      ext x
      simp only [W, Set.mem_preimage, W', Set.mem_image]
      constructor
      · intro hx; exact ⟨x, hx, rfl⟩
      · rintro ⟨x', hx', hT_eq⟩
        have h_inj : x' = x := T_equiv.injective hT_eq
        rw [h_inj] at hx'; exact hx'
    rw [h]
    exact T_equiv.measurableSet_preimage.mpr hW'_meas

  have hpres_T : MeasurePreserving T volume volume := by
    have h1 : MeasurePreserving A volume volume := A.measurePreserving
    have h2 : MeasurePreserving (fun x : Point3 => x - p) volume volume :=
      measurePreserving_sub_right volume p
    exact h1.comp h2

  have hvol1 : volume W = volume W' := by
    have hmap : Measure.map T volume = volume := hpres_T.map_eq
    have hW'image_meas : MeasurableSet (T '' W) := T_equiv.measurableSet_image.mpr hW_meas
    have h : volume (T '' W) = volume W := by
      calc
        volume (T '' W)
          = Measure.map T volume (T '' W) := by rw [hmap]
        _ = volume (T ⁻¹' (T '' W)) := Measure.map_apply hpres_T.measurable hW'image_meas
        _ = volume W := by
          have h_eq : T ⁻¹' (T '' W) = W := Set.preimage_image_eq _ T_equiv.injective
          rw [h_eq]
    exact h.symm

  have hpres_F : MeasurePreserving F volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have hcontG : Continuous G := PiLp.continuous_toLp 2 (β := fun (_ : Fin 3) => ℝ)

  let F_equiv : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := F
      invFun := G
      left_inv := WithLp.toLp_ofLp (p := 2)
      right_inv := WithLp.ofLp_toLp (p := 2)
      measurable_toFun := hpres_F.measurable
      measurable_invFun := hcontG.measurable }

  have hW''_meas : MeasurableSet W'' := F_equiv.measurableSet_image.mpr hW'_meas

  have hvol2 : volume W' = volume W'' := by
    have hmap : Measure.map F volume = volume := hpres_F.map_eq
    have h : volume W'' = volume W' := by
      calc
        volume W''
          = Measure.map F volume W'' := by rw [hmap]
        _ = volume (F ⁻¹' W'') := Measure.map_apply hpres_F.measurable hW''_meas
        _ = volume W' := by
          have h_eq : F ⁻¹' W'' = W' := Set.preimage_image_eq _ F_equiv.injective
          rw [h_eq]
    exact h.symm

  have hmain : volume W'' ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' W'') :=
    Real.volume_pi_le_prod_diam W''

  have h_ediam0 : Metric.ediam (Function.eval 0 '' W'') ≤ ENNReal.ofReal d0 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rcases ha with ⟨z, hz, rfl⟩; rcases hz with ⟨y, hy, rfl⟩
    rcases hb with ⟨z', hz', rfl⟩; rcases hz' with ⟨y', hy', rfl⟩
    rw [hW'_eq] at hy hy'
    have h6 : |(y 0 : ℝ)| ≤ d0 / 2 := hy.1
    have h7 : |(y' 0 : ℝ)| ≤ d0 / 2 := hy'.1
    have h : |(y 0 : ℝ) - (y' 0 : ℝ)| ≤ d0 := by
      calc
        |(y 0 : ℝ) - (y' 0 : ℝ)| ≤ |(y 0 : ℝ)| + |(y' 0 : ℝ)| := abs_sub _ _
        _ ≤ d0 / 2 + d0 / 2 := by gcongr
        _ = d0 := by ring
    simpa [Real.dist_eq] using h

  have h_ediam1 : Metric.ediam (Function.eval 1 '' W'') ≤ ENNReal.ofReal d1 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rcases ha with ⟨z, hz, rfl⟩; rcases hz with ⟨y, hy, rfl⟩
    rcases hb with ⟨z', hz', rfl⟩; rcases hz' with ⟨y', hy', rfl⟩
    rw [hW'_eq] at hy hy'
    have h6 : |(y 1 : ℝ)| ≤ d1 / 2 := hy.2.1
    have h7 : |(y' 1 : ℝ)| ≤ d1 / 2 := hy'.2.1
    have h : |(y 1 : ℝ) - (y' 1 : ℝ)| ≤ d1 := by
      calc
        |(y 1 : ℝ) - (y' 1 : ℝ)| ≤ |(y 1 : ℝ)| + |(y' 1 : ℝ)| := abs_sub _ _
        _ ≤ d1 / 2 + d1 / 2 := by gcongr
        _ = d1 := by ring
    simpa [Real.dist_eq] using h

  have h_ediam2 : Metric.ediam (Function.eval 2 '' W'') ≤ ENNReal.ofReal d2 := by
    apply Metric.ediam_le_of_forall_dist_le
    intro a ha b hb
    rcases ha with ⟨z, hz, rfl⟩; rcases hz with ⟨y, hy, rfl⟩
    rcases hb with ⟨z', hz', rfl⟩; rcases hz' with ⟨y', hy', rfl⟩
    rw [hW'_eq] at hy hy'
    have h6 : |(y 2 : ℝ)| ≤ d2 / 2 := hy.2.2
    have h7 : |(y' 2 : ℝ)| ≤ d2 / 2 := hy'.2.2
    have h : |(y 2 : ℝ) - (y' 2 : ℝ)| ≤ d2 := by
      calc
        |(y 2 : ℝ) - (y' 2 : ℝ)| ≤ |(y 2 : ℝ)| + |(y' 2 : ℝ)| := abs_sub _ _
        _ ≤ d2 / 2 + d2 / 2 := by gcongr
        _ = d2 := by ring
    simpa [Real.dist_eq] using h

  have hprod : (∏ i : Fin 3, Metric.ediam (Function.eval i '' W'')) ≤
      ENNReal.ofReal (d0 * d1 * d2) := by
    have h_expand : (∏ i : Fin 3, Metric.ediam (Function.eval i '' W'')) =
        Metric.ediam (Function.eval 0 '' W'') *
        Metric.ediam (Function.eval 1 '' W'') *
        Metric.ediam (Function.eval 2 '' W'') := by
      simp [Fin.prod_univ_succ] <;> ring
    rw [h_expand]
    have hmul : ENNReal.ofReal d0 * ENNReal.ofReal d1 * ENNReal.ofReal d2 =
        ENNReal.ofReal (d0 * d1 * d2) := by
      rw [← ENNReal.ofReal_mul hd0, ← ENNReal.ofReal_mul (mul_nonneg hd0 hd1)] <;> ring
    rw [← hmul]
    gcongr

  calc
    volume W = volume W' := hvol1
    _ = volume W'' := hvol2
    _ ≤ ∏ i : Fin 3, Metric.ediam (Function.eval i '' W'') := hmain
    _ ≤ ENNReal.ofReal (d0 * d1 * d2) := hprod

theorem wz1_robust_close_direction_count :
    WZ1RobustCloseDirectionCountStatement := by
  intro delta kappa C hdelta_pos hdelta_le_one hdelta_le_kappa F Y p i hp hCW
  classical
  have hkappa_pos : 0 < kappa := by linarith
  set dir_i : Point3 := (F.tube i).direction with hdir_i_def
  have hdir_i_unit : ‖dir_i‖ = 1 := (F.tube i).direction_unit
  set e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with he0_std_def
  have he0_std_unit : ‖e0_std‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  have he0_0 : e0_std 0 = 1 := by simp [e0_std, EuclideanSpace.single_apply]
  have he0_1 : e0_std 1 = 0 := by simp [e0_std, EuclideanSpace.single_apply]
  have he0_2 : e0_std 2 = 0 := by simp [e0_std, EuclideanSpace.single_apply]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 :=
    Submodule.reflection (ℝ ∙ (dir_i - e0_std))ᗮ
  have hA_dir_i : A dir_i = e0_std :=
    Submodule.reflection_sub (hdir_i_unit.trans he0_std_unit.symm)
  have hA_norm : ∀ (x : Point3), ‖A x‖ = ‖x‖ := A.norm_map
  have hcoord0 : ∀ (z : Point3), (A z) 0 = inner ℝ z dir_i := by
    intro z
    have h : (A z) 0 = inner ℝ (A z) e0_std := by
      have h2 : inner ℝ (A z) e0_std = (1 : ℝ) * (A z) 0 :=
        EuclideanSpace.inner_single_right 0 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e0_std = inner ℝ z (A.symm e0_std) := by
      have h4 := A.inner_map_map z (A.symm e0_std)
      have h5 : A (A.symm e0_std) = e0_std := A.apply_symm_apply e0_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e0_std = dir_i := by
      have h7 : A (A.symm e0_std) = A dir_i := by
        rw [A.apply_symm_apply, hA_dir_i]
      exact A.injective h7
    rw [h6]
  have hcoord_perp : ∀ (z : Point3),
      ‖z - inner ℝ z dir_i • dir_i‖ ^ 2 = |(A z) 1| ^ 2 + |(A z) 2| ^ 2 := by
    intro z
    let r := z - inner ℝ z dir_i • dir_i
    have hAr : A r = A z - inner ℝ z dir_i • e0_std := by
      have h1 : A r = A z - A (inner ℝ z dir_i • dir_i) := by
        rw [show r = z - inner ℝ z dir_i • dir_i from rfl, A.map_sub]
      rw [h1, A.map_smul, hA_dir_i] <;> rfl
    have hAr0 : (A r) 0 = 0 := by
      rw [hAr]
      have h : (A z - inner ℝ z dir_i • e0_std) 0 = (A z) 0 - inner ℝ z dir_i := by
        simp [he0_0] <;> ring
      rw [h, hcoord0] <;> ring
    have hAr1 : (A r) 1 = (A z) 1 := by
      rw [hAr]; simp [he0_1] <;> ring
    have hAr2 : (A r) 2 = (A z) 2 := by
      rw [hAr]; simp [he0_2] <;> ring
    have h_norm : ‖r‖ ^ 2 = ‖A r‖ ^ 2 := by rw [hA_norm r]
    have h_expand : ‖A r‖ ^ 2 = (A r) 0 ^ 2 + (A r) 1 ^ 2 + (A r) 2 ^ 2 :=
      point3_norm_sq (A r)
    have h_abs : ∀ (x : ℝ), |x| ^ 2 = x ^ 2 := by intro x; simp [abs_pow]
    rw [h_norm, h_expand, hAr0, hAr1, hAr2, h_abs ((A z) 1), h_abs ((A z) 2)]
    <;> ring
  set a0 : ℝ := 3 with ha0_def
  set a1 : ℝ := 3 * kappa with ha1_def
  set a2 : ℝ := 3 * kappa with ha2_def
  let W : Set Point3 := {x |
    |(A (x - p)) 0| ≤ a0 ∧ |(A (x - p)) 1| ≤ a1 ∧ |(A (x - p)) 2| ≤ a2}
  have hW_convex : Convex ℝ W := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb hab
    have h_alg : a • x + b • y - p = a • (x - p) + b • (y - p) := by
      calc
        a • x + b • y - p
          = a • x + b • y - (a + b) • p := by rw [hab] <;> simp
        _ = a • x + b • y - (a • p + b • p) := by rw [add_smul]
        _ = (a • x - a • p) + (b • y - b • p) := by abel
        _ = a • (x - p) + b • (y - p) := by
          have h4 : a • x - a • p = a • (x - p) := by rw [← smul_sub]
          have h5 : b • y - b • p = b • (y - p) := by rw [← smul_sub]
          rw [h4, h5] <;> abel
    have h_eq : A (a • x + b • y - p) = a • A (x - p) + b • A (y - p) := by
      rw [h_alg, A.map_add, A.map_smul, A.map_smul]
    have h_eval0 :
        (A (a • x + b • y - p)) 0 = a * (A (x - p)) 0 + b * (A (y - p)) 0 := by
      rw [h_eq]; simp
    have h_eval1 :
        (A (a • x + b • y - p)) 1 = a * (A (x - p)) 1 + b * (A (y - p)) 1 := by
      rw [h_eq]; simp
    have h_eval2 :
        (A (a • x + b • y - p)) 2 = a * (A (x - p)) 2 + b * (A (y - p)) 2 := by
      rw [h_eq]; simp
    have hxa0 : (A (x - p)) 0 ∈ Set.Icc (-a0) a0 := by exact abs_le.mp hx.1
    have hya0 : (A (y - p)) 0 ∈ Set.Icc (-a0) a0 := by exact abs_le.mp hy.1
    have hxa1 : (A (x - p)) 1 ∈ Set.Icc (-a1) a1 := by exact abs_le.mp hx.2.1
    have hya1 : (A (y - p)) 1 ∈ Set.Icc (-a1) a1 := by exact abs_le.mp hy.2.1
    have hxa2 : (A (x - p)) 2 ∈ Set.Icc (-a2) a2 := by exact abs_le.mp hx.2.2
    have hya2 : (A (y - p)) 2 ∈ Set.Icc (-a2) a2 := by exact abs_le.mp hy.2.2
    have h_conv0 : Convex ℝ (Set.Icc (-a0) a0) := convex_Icc (-a0) a0
    have h_conv1 : Convex ℝ (Set.Icc (-a1) a1) := convex_Icc (-a1) a1
    have h_conv2 : Convex ℝ (Set.Icc (-a2) a2) := convex_Icc (-a2) a2
    have h1 := h_conv0 hxa0 hya0 (le_of_lt ha) (le_of_lt hb) hab
    have h2 := h_conv1 hxa1 hya1 (le_of_lt ha) (le_of_lt hb) hab
    have h3 := h_conv2 hxa2 hya2 (le_of_lt ha) (le_of_lt hb) hab
    have h1' : |a * (A (x - p)) 0 + b * (A (y - p)) 0| ≤ a0 := by
      simpa [abs_le, Set.mem_Icc] using h1
    have h2' : |a * (A (x - p)) 1 + b * (A (y - p)) 1| ≤ a1 := by
      simpa [abs_le, Set.mem_Icc] using h2
    have h3' : |a * (A (x - p)) 2 + b * (A (y - p)) 2| ≤ a2 := by
      simpa [abs_le, Set.mem_Icc] using h3
    have h_goal1 : |(A (a • x + b • y - p)) 0| ≤ a0 := by
      rw [h_eval0] <;> exact h1'
    have h_goal2 : |(A (a • x + b • y - p)) 1| ≤ a1 := by
      rw [h_eval1] <;> exact h2'
    have h_goal3 : |(A (a • x + b • y - p)) 2| ≤ a2 := by
      rw [h_eval2] <;> exact h3'
    exact ⟨h_goal1, h_goal2, h_goal3⟩
  have h_containment : ∀ (j : Fin F.card),
      p ∈ Y.carrier j →
      ‖wz1Cross dir_i (F.tube j).direction‖ < kappa →
      (F.tube j).carrier ⊆ W := by
    intro j hj_p hj_cross x hx
    set dir_j : Point3 := (F.tube j).direction with hdir_j_def
    have hdir_j_unit : ‖dir_j‖ = 1 := (F.tube j).direction_unit
    have hj_p_tube : p ∈ (F.tube j).carrier := Y.subset_body j hj_p
    rcases tube_carrier_decomp hdelta_pos.le (F.tube j) p hj_p_tube with
      ⟨t_j, ht_j, e_j, he_j_norm, h_eq_p⟩
    rcases tube_carrier_decomp hdelta_pos.le (F.tube j) x hx with
      ⟨t, ht, e, he_norm, h_eq_x⟩
    have h_diff : x - p = (t - t_j) • dir_j + (e - e_j) := by
      ext k
      simp [h_eq_x, h_eq_p, hdir_j_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      <;> ring
    have h_abs_t_diff : |t - t_j| ≤ 1 := by
      have h1 : -1 ≤ t - t_j := by linarith [ht_j.1, ht_j.2, ht.1, ht.2]
      have h2 : t - t_j ≤ 1 := by linarith [ht_j.1, ht_j.2, ht.1, ht.2]
      exact abs_le.mpr ⟨h1, h2⟩
    have h_e_diff_norm : ‖e - e_j‖ ≤ 2 * delta := by
      calc
        ‖e - e_j‖ ≤ ‖e‖ + ‖e_j‖ := norm_sub_le _ _
        _ ≤ delta + delta := by linarith [he_norm, he_j_norm]
        _ = 2 * delta := by ring
    have h_e_diff_kappa : ‖e - e_j‖ ≤ 2 * kappa := by
      calc
        ‖e - e_j‖ ≤ 2 * delta := h_e_diff_norm
        _ ≤ 2 * kappa := by linarith [hdelta_le_kappa]
    have h_dist : ‖x - p‖ ≤ 3 := by
      rw [h_diff]
      calc
        ‖(t - t_j) • dir_j + (e - e_j)‖
            ≤ ‖(t - t_j) • dir_j‖ + ‖e - e_j‖ := norm_add_le _ _
        _ = |t - t_j| * ‖dir_j‖ + ‖e - e_j‖ := by
          rw [norm_smul, Real.norm_eq_abs] <;> ring
        _ ≤ 1 * 1 + 2 * delta := by gcongr <;> exact hdir_j_unit.le
        _ ≤ 3 := by linarith [hdelta_le_one]
    have h_axial : |inner ℝ (x - p) dir_i| ≤ a0 := by
      have h : |inner ℝ (x - p) dir_i| ≤ ‖x - p‖ * ‖dir_i‖ :=
        abs_real_inner_le_norm _ _
      rw [hdir_i_unit] at h
      linarith [h_dist, ha0_def]
    let radial := fun (z : Point3) => z - inner ℝ z dir_i • dir_i
    have h_inner_diff : inner ℝ (x - p) dir_i =
        (t - t_j) * inner ℝ dir_j dir_i + inner ℝ (e - e_j) dir_i := by
      rw [h_diff, inner_add_left, inner_smul_left]
      have h_star : (starRingEnd ℝ) (t - t_j) = (t - t_j) := by simp
      rw [h_star] <;> ring
    have h_radial_diff : radial (x - p) =
        (t - t_j) • radial dir_j + radial (e - e_j) := by
      ext k
      generalize hc1 : inner ℝ dir_j dir_i = c1
      generalize hc2 : inner ℝ (e - e_j) dir_i = c2
      generalize hd : dir_i k = d
      generalize hdj : dir_j k = dj
      generalize hek : (e - e_j) k = ek
      have h1 : (x - p) k = (t - t_j) * dj + ek := by
        rw [h_diff]
        simp [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, hdj, hek]
      have h2 : inner ℝ (x - p) dir_i = (t - t_j) * c1 + c2 := by
        rw [h_inner_diff, hc1, hc2]
      have h3 : (x - p) k - inner ℝ (x - p) dir_i * d =
          (t - t_j) * (dj - c1 * d) + (ek - c2 * d) := by
        rw [h1, h2] <;> ring
      have h4 : (x - p) k - inner ℝ (x - p) dir_i * d =
          (t - t_j) * (dir_j k - inner ℝ dir_j dir_i * d) +
            ((e - e_j) k - inner ℝ (e - e_j) dir_i * d) := by
        rw [hc1.symm, hc2.symm, hdj.symm, hek.symm] at h3
        exact h3
      simpa [radial, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hd] using h4
    have h_comm : inner ℝ dir_j dir_i = inner ℝ dir_i dir_j := real_inner_comm _ _
    have h_radial_eq : radial dir_j = dir_j - inner ℝ dir_i dir_j • dir_i := by
      simp [radial, h_comm] <;> rfl
    have h_radial_dir_j_norm : ‖radial dir_j‖ = ‖wz1Cross dir_i dir_j‖ := by
      rw [h_radial_eq]
      exact (radial_norm_eq_cross_norm hdir_i_unit hdir_j_unit).symm
    have h_radial_e_norm : ‖radial (e - e_j)‖ ≤ ‖e - e_j‖ :=
      perp_projection_contractive hdir_i_unit
    have h_radial_bound : ‖radial (x - p)‖ ≤ 3 * kappa := by
      rw [h_radial_diff]
      have h1 : ‖(t - t_j) • radial dir_j + radial (e - e_j)‖ ≤
          |t - t_j| * ‖radial dir_j‖ + ‖radial (e - e_j)‖ := by
        calc
          ‖(t - t_j) • radial dir_j + radial (e - e_j)‖
              ≤ ‖(t - t_j) • radial dir_j‖ + ‖radial (e - e_j)‖ := norm_add_le _ _
          _ = |t - t_j| * ‖radial dir_j‖ + ‖radial (e - e_j)‖ := by
            rw [norm_smul, Real.norm_eq_abs] <;> ring
      have h2 : |t - t_j| * ‖radial dir_j‖ + ‖radial (e - e_j)‖ ≤
          ‖wz1Cross dir_i dir_j‖ + ‖e - e_j‖ := by
        calc
          |t - t_j| * ‖radial dir_j‖ + ‖radial (e - e_j)‖
              ≤ 1 * ‖radial dir_j‖ + ‖radial (e - e_j)‖ := by gcongr
          _ = ‖radial dir_j‖ + ‖radial (e - e_j)‖ := by ring
          _ = ‖wz1Cross dir_i dir_j‖ + ‖radial (e - e_j)‖ := by
            rw [h_radial_dir_j_norm]
          _ ≤ ‖wz1Cross dir_i dir_j‖ + ‖e - e_j‖ := by gcongr
      have h3 : ‖wz1Cross dir_i dir_j‖ + ‖e - e_j‖ < 3 * kappa := by
        have h31 : ‖wz1Cross dir_i dir_j‖ < kappa := hj_cross
        have h32 : ‖e - e_j‖ ≤ 2 * kappa := h_e_diff_kappa
        linarith
      calc
        ‖(t - t_j) • radial dir_j + radial (e - e_j)‖
            ≤ |t - t_j| * ‖radial dir_j‖ + ‖radial (e - e_j)‖ := h1
        _ ≤ ‖wz1Cross dir_i dir_j‖ + ‖e - e_j‖ := h2
        _ ≤ 3 * kappa := le_of_lt h3
    have h_coord0 : |(A (x - p)) 0| ≤ a0 := by
      rw [hcoord0] <;> exact h_axial
    have h_perp_sq :
        |(A (x - p)) 1| ^ 2 + |(A (x - p)) 2| ^ 2 ≤ (3 * kappa) ^ 2 := by
      have h : ‖radial (x - p)‖ ^ 2 =
          |(A (x - p)) 1| ^ 2 + |(A (x - p)) 2| ^ 2 :=
        hcoord_perp (x - p)
      have h' : ‖radial (x - p)‖ ^ 2 ≤ (3 * kappa) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h_radial_bound 2
      rw [h] at h'
      exact h'
    have h_coord1 : |(A (x - p)) 1| ≤ a1 := by
      have h9 : |(A (x - p)) 1| ^ 2 ≤ (3 * kappa) ^ 2 := by
        have h2 : 0 ≤ |(A (x - p)) 2| ^ 2 := by positivity
        linarith [h_perp_sq]
      have h4 : 0 ≤ 3 * kappa := by positivity
      have h5 : |(A (x - p)) 1| ≤ 3 * kappa := abs_le_of_sq_le h4 h9
      simpa [ha1_def] using h5
    have h_coord2 : |(A (x - p)) 2| ≤ a2 := by
      have h9 : |(A (x - p)) 2| ^ 2 ≤ (3 * kappa) ^ 2 := by
        have h2 : 0 ≤ |(A (x - p)) 1| ^ 2 := by positivity
        linarith [h_perp_sq]
      have h4 : 0 ≤ 3 * kappa := by positivity
      have h5 : |(A (x - p)) 2| ≤ 3 * kappa := abs_le_of_sq_le h4 h9
      simpa [ha2_def] using h5
    exact ⟨h_coord0, h_coord1, h_coord2⟩
  have h_volume : volume W ≤ ENNReal.ofReal (216 * kappa ^ 2) := by
    have hW_eq : W = {x : Point3 |
        |(A (x - p)) 0| ≤ (6 : ℝ) / 2 ∧
        |(A (x - p)) 1| ≤ (6 * kappa) / 2 ∧
        |(A (x - p)) 2| ≤ (6 * kappa) / 2} := by
      ext x
      simp only [W, ha0_def, ha1_def, ha2_def, Set.mem_setOf_eq]
      <;> ring_nf
      <;> rfl
    rw [hW_eq]
    have hd0 : 0 ≤ (6 : ℝ) := by norm_num
    have hd1 : 0 ≤ 6 * kappa := by
      have h : 0 < kappa := hkappa_pos
      exact mul_nonneg (by norm_num) (by linarith)
    have hd2 : 0 ≤ 6 * kappa := by
      have h : 0 < kappa := hkappa_pos
      exact mul_nonneg (by norm_num) (by linarith)
    have h_main := oriented_box_volume_bound A p 6 (6 * kappa) (6 * kappa) hd0 hd1 hd2
    have h_mul : (6 : ℝ) * (6 * kappa) * (6 * kappa) = 216 * kappa ^ 2 := by ring
    rw [h_mul] at h_main
    exact h_main
  let S : Finset (Fin F.card) := Finset.univ.filter fun j =>
    p ∈ Y.carrier j ∧ ‖wz1Cross dir_i (F.tube j).direction‖ < kappa
  have hS_sub : S ⊆ F.toBodyFamily.containedIndices W := by
    intro j hj
    have h_j_in_S :
        p ∈ Y.carrier j ∧ ‖wz1Cross dir_i (F.tube j).direction‖ < kappa :=
      (Finset.mem_filter.mp hj).2
    have h_cont : (F.tube j).carrier ⊆ W :=
      h_containment j h_j_in_S.1 h_j_in_S.2
    have h_body_eq : (F.toBodyFamily.body j).carrier = (F.tube j).carrier := by rfl
    have h_body_cont : (F.toBodyFamily.body j).carrier ⊆ W := by
      rw [h_body_eq]; exact h_cont
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_body_cont⟩
  have h_card : S.card ≤ (F.toBodyFamily.containedIndices W).card :=
    Finset.card_le_card hS_sub
  have h_count_le : (S.card : ENNReal) ≤ F.toBodyFamily.containedCount W := by
    dsimp only [Kakeya.Streamlined.BodyFamily.containedCount]
    exact_mod_cast h_card
  have hCW' := hCW W hW_convex
  have h_final : (S.card : ENNReal) * Kakeya.deltaTubeVolume 1 ≤
      C * ENNReal.ofReal (216 * kappa ^ 2) * F.enncard := by
    calc
      (S.card : ENNReal) * Kakeya.deltaTubeVolume 1
          ≤ F.toBodyFamily.containedCount W * Kakeya.deltaTubeVolume 1 := by gcongr
      _ ≤ C * volume W * F.enncard := hCW'
      _ ≤ C * ENNReal.ofReal (216 * kappa ^ 2) * F.enncard := by
        gcongr <;> exact h_volume
  have hS_eq : S.card = wz1CloseDirectionCount Y p i kappa := by rfl
  rw [hS_eq] at h_final
  exact ⟨W, hW_convex, h_volume, h_containment, h_final⟩

end Kakeya.Assouad
