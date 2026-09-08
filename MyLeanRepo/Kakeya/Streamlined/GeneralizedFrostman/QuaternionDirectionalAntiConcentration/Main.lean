import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.QuaternionDirectionalAntiConcentration.QuaternionRotation
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.QuaternionDirectionalAntiConcentration.SphereGrowth
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.QuaternionDirectionalAntiConcentration.HopfFiberDistance
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.QuaternionDirectionalAntiConcentration.MeasureTransport
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.DirectionalAntiConcentration

noncomputable section

open scoped Quaternion RealInnerProductSpace

open Quaternion Metric MeasureTheory Set Finset
open SeedMathlib.Topology.Homotopy.Pi3Sphere2

namespace Kakeya.Streamlined.GeneralizedFrostman

/-! ## Right multiplication on QuatSphere3 -/

noncomputable def rightMul (p : QuatSphere3) (q : QuatSphere3) : QuatSphere3 :=
  let q1 : ℍ := q.val * p.val
  have h_norm : ‖q1‖ = 1 := by
    rw [norm_mul, sphere3_norm_eq_one q, sphere3_norm_eq_one p] <;> ring
  ⟨q1, by simpa [dist_zero_right, Metric.mem_sphere] using h_norm⟩

noncomputable def rightMulEquiv (p : QuatSphere3) : QuatSphere3 ≃ᵢ QuatSphere3 :=
  let p_inv_val : ℍ := star p.val
  have hp_inv_norm : ‖p_inv_val‖ = 1 := by
    rw [_root_.norm_star, sphere3_norm_eq_one p]
  let p_inv : QuatSphere3 := ⟨p_inv_val, by simpa [dist_zero_right, Metric.mem_sphere] using hp_inv_norm⟩
  have h_normSq : normSq p.val = 1 := by
    rw [normSq_eq_norm_mul_self, sphere3_norm_eq_one p] <;> ring
  have h_mul_star : p.val * star p.val = (1 : ℍ) := by
    have h : p.val * star p.val = ↑(normSq p.val) := self_mul_star p.val
    rw [h, h_normSq] <;> simp
  have h_star_mul : star p.val * p.val = (1 : ℍ) := by
    have h : star p.val * p.val = ↑(normSq p.val) := star_mul_self p.val
    rw [h, h_normSq] <;> simp
  have h_right_inv : ∀ (q : QuatSphere3), rightMul p (rightMul p_inv q) = q := by
    intro q
    apply Subtype.ext
    have h1 : (rightMul p (rightMul p_inv q)).val = (rightMul p_inv q).val * p.val := by rfl
    have h2 : (rightMul p_inv q).val = q.val * star p.val := by rfl
    rw [h1, h2, mul_assoc, h_star_mul, mul_one]
  have h_left_inv : ∀ (q : QuatSphere3), rightMul p_inv (rightMul p q) = q := by
    intro q
    apply Subtype.ext
    have h1 : (rightMul p_inv (rightMul p q)).val = (rightMul p q).val * star p.val := by rfl
    have h2 : (rightMul p q).val = q.val * p.val := by rfl
    rw [h1, h2, mul_assoc, h_mul_star, mul_one]
  have h_isom : Isometry (rightMul p) :=
    Isometry.of_dist_eq fun q1 q2 => by
      have h2 : (rightMul p q1).val - (rightMul p q2).val = (q1.val - q2.val) * p.val := by
        simp [rightMul, sub_mul] <;> ring
      have h3 : dist (rightMul p q1) (rightMul p q2) = ‖(rightMul p q1).val - (rightMul p q2).val‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]
      have h4 : dist q1 q2 = ‖q1.val - q2.val‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]
      rw [h3, h2, norm_mul, sphere3_norm_eq_one p, h4] <;> ring
  { toEquiv :=
      { toFun := rightMul p
        invFun := rightMul p_inv
        left_inv := h_left_inv
        right_inv := h_right_inv }
    isometry_toFun := h_isom }

lemma hopfMap_rightMul (p q : QuatSphere3) :
    (hopfMap (rightMul p q)).val = q.val * (hopfMap p).val * star q.val := by
  have h2 : (rightMul p q).val = q.val * p.val := by rfl
  have h4 : star (q.val * p.val) = star p.val * star q.val := star_mul q.val p.val
  calc
    (hopfMap (rightMul p q)).val
      = (rightMul p q).val * iQuat * star (rightMul p q).val := by rfl
    _ = (q.val * p.val) * iQuat * star (q.val * p.val) := by rw [h2]
    _ = (q.val * p.val) * iQuat * (star p.val * star q.val) := by rw [h4]
    _ = q.val * (p.val * iQuat * star p.val) * star q.val := by
      simp [mul_assoc] <;> rfl
    _ = q.val * (hopfMap p).val * star q.val := by rfl

/-! ## Isometry between QuatSphere3 and Sphere3 -/

noncomputable def sphere3IsometryEuclidean4 : QuatSphere3 ≃ᵢ Sphere3 :=
  have h_isom : Isometry (sphere3HomeoEuclidean4 : QuatSphere3 → Sphere3) :=
    Isometry.of_dist_eq fun q1 q2 => by
      have h1 : dist (sphere3HomeoEuclidean4 q1) (sphere3HomeoEuclidean4 q2) =
                   ‖(sphere3HomeoEuclidean4 q1).val - (sphere3HomeoEuclidean4 q2).val‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]
      have h2 : dist q1 q2 = ‖q1.val - q2.val‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]
      have h3 : (sphere3HomeoEuclidean4 q1).val - (sphere3HomeoEuclidean4 q2).val =
                   quaternionToEuclidean4 (q1.val - q2.val) := by
        simp [sphere3HomeoEuclidean4, quaternionToEuclidean4.map_sub] <;> abel
      rw [h1, h2, h3, quaternionToEuclidean4.norm_map]
  { toEquiv := sphere3HomeoEuclidean4.toEquiv
    isometry_toFun := h_isom }

/-! ## Main theorem -/

theorem quaternion_directional_anti_concentration_main :
    QuaternionDirectionalAntiConcentrationStatement := by
  classical
  let μ : Measure Sphere3 := sphere3ProbabilityMeasure
  let rotation : Sphere3 → (Point3 ≃ₗᵢ[ℝ] Point3) := euclideanRotation
  have h_meas : ∀ u : Point3, Measurable fun q : Sphere3 => rotation q u :=
    measurable_euclideanRotation_eval
  have h_prob : IsProbabilityMeasure μ := sphere3ProbabilityMeasure_isProbability

  let hIso : QuatSphere3 ≃ᵢ Sphere3 := sphere3IsometryEuclidean4
  let ν : Measure QuatSphere3 := Measure.map hIso.symm μ

  let K : ENNReal := (volume.toSphere (Set.univ : Set Sphere3))⁻¹
  let C_growth : ENNReal := K * ENNReal.ofReal 32

  have hK_pos : 0 < volume.toSphere (Set.univ : Set Sphere3) := by
    exact NeZero.pos (volume.toSphere Set.univ)
  have hK_ne_top : volume.toSphere (Set.univ : Set Sphere3) ≠ ⊤ :=
    measure_ne_top volume.toSphere (Set.univ : Set Sphere3)

  have h_growth_μ : ∀ (y : Sphere3) (r : ℝ), 0 < r → r ≤ 1 →
      μ (closedBall y r) ≤ C_growth * ENNReal.ofReal (r ^ 3) := by
    intro y r hr hr1
    have h := sphere3_growth (x := y) hr hr1
    have h2 : ENNReal.ofReal (32 * r ^ 3) * K = C_growth * ENNReal.ofReal (r ^ 3) := by
      simp only [C_growth]
      have h3 : ENNReal.ofReal (32 * r ^ 3) = ENNReal.ofReal 32 * ENNReal.ofReal (r ^ 3) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
      rw [h3] <;> ring
    rw [h2] at h
    exact h

  have h_growth_ν : ∀ (x : QuatSphere3) (r : ℝ), 0 < r → r ≤ 1 →
      ν (closedBall x r) ≤ C_growth * ENNReal.ofReal (r ^ 3) :=
    transport_ball_growth hIso μ C_growth h_growth_μ

  let c : ℝ := 1 / 4 + 1 / Real.sqrt 2
  have hc_pos : 0 < c := by positivity
  have hc_lt_one : c < 1 := by
    have h1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h2 : Real.sqrt 2 < 3 / 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have h3 : 1 / Real.sqrt 2 < 3 / 4 := by
      have h4 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
        field_simp [h1.ne'] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      rw [h4]
      linarith
    have h5 : c = 1 / 4 + 1 / Real.sqrt 2 := by rfl
    rw [h5]
    linarith

  let C_cap : ENNReal := ENNReal.ofReal ((8 * Real.pi + 1) * c ^ 3) * C_growth
  let C : ENNReal := max 1 (2 * C_cap)
  have hC_one : 1 ≤ C := le_max_left _ _
  have hK' : K ≠ ⊤ := ENNReal.inv_ne_top.mpr hK_pos.ne'
  have hCg : C_growth ≠ ⊤ := ENNReal.mul_ne_top hK' ENNReal.ofReal_ne_top
  have hCc : C_cap ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCg
  have hC_top : C ≠ ⊤ := by
    simp only [C]
    have h1 : (1 : ENNReal) ≠ ⊤ := by simp
    have h2 : 2 * C_cap ≠ ⊤ := ENNReal.mul_ne_top (by simp) hCc
    have h3 : max 1 (2 * C_cap) ≤ 1 + (2 * C_cap) := by
      exact max_le (le_add_right le_rfl) (le_add_left le_rfl)
    have h4 : 1 + (2 * C_cap) ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h1, h2⟩
    exact ne_top_of_le_ne_top h4 h3

  have h_cap_bound : ∀ (u v : Point3), ‖u‖ = 1 → ‖v‖ = 1 →
      ∀ (alpha : ℝ), 0 < alpha → alpha ≤ 1 →
        μ {q : Sphere3 | ‖rotation q u - v‖ ≤ alpha} ≤
          C_cap * ENNReal.ofReal (alpha ^ 2) := by
    intro u v hu hv alpha hα hα1

    let u' : ℍ := (point3ToImaginary u).val
    let v' : ℍ := (point3ToImaginary v).val
    have hu'_re : u'.re = 0 := (point3ToImaginary u).property
    have hu'_norm : ‖u'‖ = 1 := by
      have h : ‖u'‖ = ‖u‖ := point3ToImaginary.norm_map u
      rw [h, hu]
    have hv'_re : v'.re = 0 := (point3ToImaginary v).property
    have hv'_norm : ‖v'‖ = 1 := by
      have h : ‖v'‖ = ‖v‖ := point3ToImaginary.norm_map v
      rw [h, hv]

    let u_quat : QuatSphere2 := ⟨u', ⟨hu'_re, hu'_norm⟩⟩
    let v_quat : QuatSphere2 := ⟨v', ⟨hv'_re, hv'_norm⟩⟩

    rcases hopfMap_surjective u_quat with ⟨p, hp⟩
    let rmul : QuatSphere3 ≃ᵢ QuatSphere3 := rightMulEquiv p

    let T_v : Set QuatSphere3 := {r | ‖(hopfMap r).val - v'‖ ≤ alpha}
    let s_v : Set QuatSphere3 := rmul⁻¹' T_v

    have h_rot_eq : ∀ (q : QuatSphere3),
        quaternionRotationSphere q u =
          point3ToImaginary.symm
            (⟨q.val * u' * star q.val,
              quaternionConj_preserves_imaginary q.val
                (by have h : dist q.val 0 = 1 := q.property
                    simpa [dist_zero_right] using h)
                (point3ToImaginary u).property⟩) := by
      intro q
      simp [quaternionRotationSphere, quaternionRotation, quaternionConjImaginary,
        point3ToImaginary, u'] <;> rfl

    have h_norm_eq : ∀ (q : QuatSphere3),
        ‖quaternionRotationSphere q u - v‖ = ‖q.val * u' * star q.val - v'‖ := by
      intro q
      have h1 : point3ToImaginary (quaternionRotationSphere q u) =
          (⟨q.val * u' * star q.val,
            quaternionConj_preserves_imaginary q.val
              (by have h : dist q.val 0 = 1 := q.property
                  simpa [dist_zero_right] using h)
              (point3ToImaginary u).property⟩ : imaginaryQuaternions) := by
        rw [h_rot_eq q] <;> simp
      have h2 : ‖quaternionRotationSphere q u - v‖ =
          ‖point3ToImaginary (quaternionRotationSphere q u) - point3ToImaginary v‖ := by
        rw [← point3ToImaginary.norm_map (quaternionRotationSphere q u - v)]
        rw [point3ToImaginary.map_sub]
      rw [h2, h1] <;> rfl

    have h_s_v_eq : s_v = {q : QuatSphere3 | ‖quaternionRotationSphere q u - v‖ ≤ alpha} := by
      ext q
      simp only [s_v, T_v, Set.mem_preimage, Set.mem_setOf_eq]
      have h_rmul_eq : rmul q = rightMul p q := by rfl
      have h_hopf : (hopfMap (rmul q)).val = q.val * (hopfMap p).val * star q.val := by
        rw [h_rmul_eq]
        exact hopfMap_rightMul p q
      have h9 : (hopfMap p).val = u' := by
        have h10 : hopfMap p = u_quat := hp
        rw [h10] <;> rfl
      have h1 : (hopfMap (rmul q)).val = q.val * u' * star q.val := by
        rw [h_hopf, h9]
      have h2 : ‖(hopfMap (rmul q)).val - v'‖ ≤ alpha ↔
          ‖quaternionRotationSphere q u - v‖ ≤ alpha := by
        rw [h1, h_norm_eq q]
      exact h2

    have h_cont_hopf : Continuous fun r : QuatSphere3 => (hopfMap r).val := by
      have h1 : Continuous (fun r : QuatSphere3 => r.val) := continuous_subtype_val
      have h2 : Continuous (fun q : ℍ => q * iQuat * star q) := by fun_prop
      exact h2.comp h1
    have h_cont_norm : Continuous fun r : QuatSphere3 => ‖(hopfMap r).val - v'‖ := by
      fun_prop
    have h_meas_T : MeasurableSet T_v :=
      measurableSet_Iic.preimage h_cont_norm.measurable
    have h_meas_sv : MeasurableSet s_v :=
      h_meas_T.preimage rmul.continuous.measurable

    let S : Set Sphere3 := {q | ‖rotation q u - v‖ ≤ alpha}

    have h_image_eq : hIso '' s_v = S := by
      ext x
      simp only [S, Set.mem_image, Set.mem_setOf_eq]
      constructor
      · rintro ⟨q, hq, rfl⟩
        have h3 : hIso q ∈ S := by
          simp only [S, Set.mem_setOf_eq]
          have h4 : rotation (hIso q) u = quaternionRotationSphere q u := by rfl
          rw [h4]
          have h5 : q ∈ s_v := hq
          rw [h_s_v_eq] at h5
          exact h5
        exact h3
      · intro hx
        let q : QuatSphere3 := hIso.symm x
        have hq1 : hIso q = x := hIso.apply_symm_apply x
        have hq2 : q ∈ s_v := by
          rw [h_s_v_eq]
          simp only [Set.mem_setOf_eq]
          have h3 : rotation x u = quaternionRotationSphere q u := by
            have h4 : x = hIso q := hq1.symm
            rw [h4] <;> rfl
          exact h3 ▸ hx
        exact ⟨q, hq2, hq1⟩

    have hμ_eq : μ S = ν s_v := by
      have h : ν s_v = μ (hIso '' s_v) := transport_set_measure hIso μ h_meas_sv
      have h' : hIso '' s_v = S := h_image_eq
      rw [h'] at h
      exact h.symm

    have hα4 : 0 < alpha / 4 := by positivity
    rcases fiber_cover hα4 v_quat with ⟨s, hcover, hcard⟩

    have hcover2 : T_v ⊆ ⋃ x ∈ s, ball x (c * alpha) := by
      intro r hr
      have h_in_T : ‖(hopfMap r).val - v'‖ ≤ alpha := by
        simpa [T_v, Set.mem_setOf_eq] using hr
      have h_vq_val : v_quat.val = v' := by rfl
      rcases exists_close_to_fiber v_quat r with ⟨p_fiber, hpf_fiber, hpf_dist⟩
      have h_bound : ‖(hopfMap r).val - v_quat.val‖ ≤ alpha := by
        rw [h_vq_val]
        exact h_in_T
      have hpf_dist' : ‖r.val - p_fiber.val‖ ≤ (1 / Real.sqrt 2) * alpha := by
        calc ‖r.val - p_fiber.val‖
          ≤ (1 / Real.sqrt 2) * ‖(hopfMap r).val - v_quat.val‖ := hpf_dist
        _ ≤ (1 / Real.sqrt 2) * alpha := by gcongr
      have h_in_fiber_cover : p_fiber ∈ ⋃ x ∈ s, ball x (alpha / 4) := hcover hpf_fiber
      rcases mem_iUnion₂.mp h_in_fiber_cover with ⟨x, hx, hxb⟩
      have h_dist1 : dist r p_fiber ≤ (1 / Real.sqrt 2) * alpha := by
        simpa [Subtype.dist_eq, dist_eq_norm] using hpf_dist'
      have h_dist2 : dist p_fiber x < alpha / 4 := hxb
      have h_sum : dist r p_fiber + dist p_fiber x < (1 / Real.sqrt 2) * alpha + alpha / 4 := by
        linarith
      have h_eq : (1 / Real.sqrt 2) * alpha + alpha / 4 = c * alpha := by
        simp [c] <;> ring
      have h_dist3 : dist r x < c * alpha := by
        have h : dist r x ≤ dist r p_fiber + dist p_fiber x := dist_triangle _ _ _
        linarith
      exact mem_iUnion₂.mpr ⟨x, hx, h_dist3⟩

    have hcover3 : s_v ⊆ ⋃ x ∈ s, ball (rmul.symm x) (c * alpha) := by
      intro q hq
      have h4 : rmul q ∈ T_v := hq
      have h5 : rmul q ∈ ⋃ x ∈ s, ball x (c * alpha) := hcover2 h4
      rcases mem_iUnion₂.mp h5 with ⟨x, hx, hxb⟩
      have h6 : dist q (rmul.symm x) < c * alpha := by
        have h7 : dist (rmul q) x < c * alpha := hxb
        have h8 : dist q (rmul.symm x) = dist (rmul q) x := by
          have h9 : dist (rmul q) (rmul (rmul.symm x)) = dist q (rmul.symm x) :=
            rmul.dist_eq q (rmul.symm x)
          have h10 : rmul (rmul.symm x) = x := rmul.apply_symm_apply x
          rw [h10] at h9
          exact h9.symm
        rw [h8]
        exact h7
      exact mem_iUnion₂.mpr ⟨x, hx, h6⟩

    have hR_pos : 0 < c * alpha := mul_pos hc_pos hα
    have hR_le_one : c * alpha ≤ 1 := by
      have h : c * alpha ≤ c * 1 := by
        exact mul_le_mul_of_nonneg_left hα1 (by positivity)
      have h2 : c * 1 = c := by ring
      rw [h2] at h
      exact h.trans hc_lt_one.le

    have h_ball_meas : ∀ (x : QuatSphere3),
        ν (ball x (c * alpha)) ≤ C_growth * ENNReal.ofReal ((c * alpha) ^ 3) := by
      intro x
      have h : ν (ball x (c * alpha)) ≤ ν (closedBall x (c * alpha)) :=
        measure_mono ball_subset_closedBall
      have h2 : ν (closedBall x (c * alpha)) ≤ C_growth * ENNReal.ofReal ((c * alpha) ^ 3) :=
        h_growth_ν x (c * alpha) hR_pos hR_le_one
      exact h.trans h2

    have h_sum1 : ν s_v ≤ ∑ x ∈ s, ν (ball (rmul.symm x) (c * alpha)) := by
      calc ν s_v
        ≤ ν (⋃ x ∈ s, ball (rmul.symm x) (c * alpha)) := ν.mono hcover3
      _ ≤ ∑ x ∈ s, ν (ball (rmul.symm x) (c * alpha)) := by
        exact measure_biUnion_finset_le s (fun x => ball (rmul.symm x) (c * alpha))

    have h_sum_le : ∑ x ∈ s, ν (ball (rmul.symm x) (c * alpha)) ≤
        ∑ x ∈ s, C_growth * ENNReal.ofReal ((c * alpha) ^ 3) := by
      apply Finset.sum_le_sum
      intro i _
      exact h_ball_meas (rmul.symm i)
    have h_sum_const : ∑ x ∈ s, C_growth * ENNReal.ofReal ((c * alpha) ^ 3) =
        (s.card : ENNReal) * C_growth * ENNReal.ofReal ((c * alpha) ^ 3) := by
      simp [Finset.sum_const] <;> ring
    have h_sum2' : ν s_v ≤ (s.card : ENNReal) * C_growth * ENNReal.ofReal ((c * alpha) ^ 3) := by
      calc ν s_v
        ≤ ∑ x ∈ s, ν (ball (rmul.symm x) (c * alpha)) := h_sum1
      _ ≤ ∑ x ∈ s, C_growth * ENNReal.ofReal ((c * alpha) ^ 3) := h_sum_le
      _ = (s.card : ENNReal) * C_growth * ENNReal.ofReal ((c * alpha) ^ 3) := h_sum_const

    have hcard2 : (s.card : ENNReal) ≤ ENNReal.ofReal ((8 * Real.pi + 1) / alpha) := by
      have h1 : s.card ≤ Nat.ceil (2 * Real.pi / (alpha / 4)) := hcard
      have h2 : 2 * Real.pi / (alpha / 4) = 8 * Real.pi / alpha := by ring
      rw [h2] at h1
      have h31 : (s.card : ℝ) ≤ Nat.ceil (8 * Real.pi / alpha) := by exact_mod_cast h1
      have h32 : Nat.ceil (8 * Real.pi / alpha) ≤ 8 * Real.pi / alpha + 1 := by
        have h : (Nat.ceil (8 * Real.pi / alpha) : ℝ) < (8 * Real.pi / alpha) + 1 :=
          Nat.ceil_lt_add_one (ha := by positivity)
        exact_mod_cast h.le
      have h3 : (s.card : ℝ) ≤ 8 * Real.pi / alpha + 1 := by linarith
      have h4 : 8 * Real.pi / alpha + 1 ≤ (8 * Real.pi + 1) / alpha := by
        have h5 : 0 < alpha := hα
        calc 8 * Real.pi / alpha + 1
          = (8 * Real.pi + alpha) / alpha := by field_simp [h5.ne'] <;> ring
        _ ≤ (8 * Real.pi + 1) / alpha := by gcongr
      have h7 : (s.card : ℝ) ≤ (8 * Real.pi + 1) / alpha := by linarith
      have h8 : (s.card : ENNReal) ≤ ENNReal.ofReal ((8 * Real.pi + 1) / alpha) := by
        have h9 : (s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) := by simp
        rw [h9]
        exact ENNReal.ofReal_le_ofReal h7
      exact h8

    have h_final : ν s_v ≤ C_cap * ENNReal.ofReal (alpha ^ 2) := by
      calc ν s_v
        ≤ (s.card : ENNReal) * C_growth * ENNReal.ofReal ((c * alpha) ^ 3) := h_sum2'
      _ ≤ ENNReal.ofReal ((8 * Real.pi + 1) / alpha) * C_growth *
              ENNReal.ofReal ((c * alpha) ^ 3) := by gcongr
      _ = C_cap * ENNReal.ofReal (alpha ^ 2) := by
        simp only [C_cap]
        have h_pos1 : 0 ≤ (8 * Real.pi + 1) / alpha := by positivity
        have h_pos2 : 0 ≤ (c * alpha) ^ 3 := by positivity
        have h_eq1 : ENNReal.ofReal ((8 * Real.pi + 1) / alpha) *
                        ENNReal.ofReal ((c * alpha) ^ 3) =
                    ENNReal.ofReal (((8 * Real.pi + 1) / alpha) * (c * alpha) ^ 3) := by
          rw [← ENNReal.ofReal_mul h_pos1]
        have h_eq2 : ((8 * Real.pi + 1) / alpha) * (c * alpha) ^ 3 =
            (8 * Real.pi + 1) * c ^ 3 * alpha ^ 2 := by
          field_simp [hα.ne'] <;> ring
        have h_main : ENNReal.ofReal ((8 * Real.pi + 1) / alpha) * C_growth * ENNReal.ofReal ((c * alpha) ^ 3) =
                        ENNReal.ofReal ((8 * Real.pi + 1) * c ^ 3) * C_growth * ENNReal.ofReal (alpha ^ 2) := by
          have h_assoc : ENNReal.ofReal ((8 * Real.pi + 1) / alpha) * C_growth * ENNReal.ofReal ((c * alpha) ^ 3) =
              C_growth * (ENNReal.ofReal ((8 * Real.pi + 1) / alpha) * ENNReal.ofReal ((c * alpha) ^ 3)) := by ring
          rw [h_assoc, h_eq1]
          rw [h_eq2]
          have h_eq3 : ENNReal.ofReal ((8 * Real.pi + 1) * c ^ 3 * alpha ^ 2) =
              ENNReal.ofReal ((8 * Real.pi + 1) * c ^ 3) * ENNReal.ofReal (alpha ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
          rw [h_eq3] <;> ring
        exact h_main

    rw [hμ_eq]
    exact h_final

  refine' ⟨μ, h_prob, rotation, h_meas, C, hC_one, hC_top, _⟩
  intro u v hu hv alpha hα hα1
  let S1 : Set Sphere3 := {q | ‖rotation q u - v‖ ≤ alpha}
  let S2 : Set Sphere3 := {q | ‖rotation q u + v‖ ≤ alpha}
  have h1 : μ S1 ≤ C_cap * ENNReal.ofReal (alpha ^ 2) :=
    h_cap_bound u v hu hv alpha hα hα1
  have h2 : μ S2 ≤ C_cap * ENNReal.ofReal (alpha ^ 2) := by
    have h3 : ‖-v‖ = 1 := by
      simp [hv]
    have h4 := h_cap_bound u (-v) hu h3 alpha hα hα1
    simpa [S2] using h4
  have h5 : μ (S1 ∪ S2) ≤ μ S1 + μ S2 := measure_union_le _ _
  have h6 : μ S1 + μ S2 ≤ 2 * C_cap * ENNReal.ofReal (alpha ^ 2) := by
    calc μ S1 + μ S2
      ≤ C_cap * ENNReal.ofReal (alpha ^ 2) + C_cap * ENNReal.ofReal (alpha ^ 2) := by gcongr
    _ = 2 * C_cap * ENNReal.ofReal (alpha ^ 2) := by ring
  have h7 : 2 * C_cap * ENNReal.ofReal (alpha ^ 2) ≤ C * ENNReal.ofReal (alpha ^ 2) := by
    gcongr
    <;> exact le_max_right _ _
  exact h5.trans (h6.trans h7)

end Kakeya.Streamlined.GeneralizedFrostman
