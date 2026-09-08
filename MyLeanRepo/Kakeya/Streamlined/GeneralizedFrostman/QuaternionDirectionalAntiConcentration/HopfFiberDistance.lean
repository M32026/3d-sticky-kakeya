/-
# Fiber Neighborhood Covering Lemma

Direct algebraic proof that dist(q, Hopf fiber) ≤ (1/√2) * ‖hopfMap(q) - v‖,
plus fiber parameterization and covering by O(1/α) balls.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open scoped Quaternion RealInnerProductSpace
open Quaternion Metric Finset Set Complex

namespace SeedMathlib.Topology.Homotopy.Pi3Sphere2

/-! ## Basic definitions -/

def iQuat : ℍ := ⟨0, 1, 0, 0⟩

theorem norm_iQuat : ‖iQuat‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, inner_self, normSq_def']
  simp [iQuat]

theorem star_iQuat : star iQuat = -iQuat := by
  apply QuaternionAlgebra.ext <;> simp [iQuat]

abbrev QuatSphere3 : Type := Metric.sphere (0 : ℍ) 1

theorem sphere3_norm_eq_one (q : QuatSphere3) : ‖(q : ℍ)‖ = 1 := by
  have h : dist (q : ℍ) 0 = 1 := q.property
  rw [dist_zero_right] at h
  exact h

def isPurelyImaginaryUnit (v : ℍ) : Prop := v.re = 0 ∧ ‖v‖ = 1

abbrev QuatSphere2 : Type := {v : ℍ // isPurelyImaginaryUnit v}

noncomputable def iQuatSphere2 : QuatSphere2 :=
  ⟨iQuat, ⟨by simp [iQuat], norm_iQuat⟩⟩

lemma hopfMap_aux_re_eq_zero (q : ℍ) : (q * iQuat * star q).re = 0 := by
  let h := q * iQuat * star q
  have h1 : star h = -h := by
    dsimp only [h]
    calc star (q * iQuat * star q)
        = star (star q) * star (q * iQuat) := by rw [star_mul]
      _ = star (star q) * (star iQuat * star q) := by rw [star_mul]
      _ = q * (star iQuat * star q) := by rw [star_star]
      _ = q * ((-iQuat) * star q) := by rw [star_iQuat]
      _ = -(q * iQuat * star q) := by simp [mul_assoc]
  have h2 : (star h).re = h.re := by simp [re_star]
  have h3 : (star h).re = (-h).re := by rw [h1]
  have h4 : (-h).re = -h.re := by simp
  have h5 : (star h).re = -h.re := by rw [h3, h4]
  have h6 : h.re = -h.re := h2.symm.trans h5
  have h7 : (2 : ℝ) * h.re = 0 := by linarith
  have h8 : h.re = 0 := by linarith
  exact h8

lemma hopfMap_aux_norm (q : ℍ) : ‖q * iQuat * star q‖ = ‖q‖ * ‖q‖ := by
  calc
    ‖q * iQuat * star q‖
      = ‖q * iQuat‖ * ‖star q‖ := norm_mul (q * iQuat) (star q)
    _ = (‖q‖ * ‖iQuat‖) * ‖star q‖ := by rw [norm_mul q iQuat]
    _ = (‖q‖ * ‖iQuat‖) * ‖q‖ := by rw [Quaternion.norm_star q]
    _ = ‖q‖ * ‖q‖ := by rw [norm_iQuat] <;> ring

noncomputable def hopfMap (q : QuatSphere3) : QuatSphere2 :=
  let q' : ℍ := q.val
  let h : ℍ := q' * iQuat * star q'
  ⟨h, ⟨hopfMap_aux_re_eq_zero q', by
    have h4 : ‖h‖ = ‖q'‖ * ‖q'‖ := hopfMap_aux_norm q'
    have h5 : ‖q'‖ = 1 := sphere3_norm_eq_one q
    rw [h4, h5] <;> ring⟩⟩

def fiber (v : QuatSphere2) : Set QuatSphere3 := {q | hopfMap q = v}

/-! ## Surjectivity -/

theorem hopfMap_surjective : Function.Surjective (hopfMap : QuatSphere3 → QuatSphere2) := by
  intro v
  let vq : ℍ := v.val
  have hv_re : vq.re = 0 := v.property.1
  have hv_norm : ‖vq‖ = 1 := v.property.2
  have hv_normSq : normSq vq = 1 := by
    rw [normSq_eq_norm_mul_self, hv_norm] <;> ring
  by_cases h_case : vq = -iQuat
  · let jQuat : ℍ := ⟨0, 0, 1, 0⟩
    have h_j_norm : ‖jQuat‖ = 1 := by
      have h1 : ‖jQuat‖ ^ 2 = normSq jQuat := by rw [normSq_eq_norm_mul_self, pow_two]
      have h2 : normSq jQuat = 1 := by simp [jQuat, normSq_def']
      have h3 : ‖jQuat‖ ^ 2 = 1 := by linarith
      have h4 : 0 ≤ ‖jQuat‖ := by positivity
      nlinarith
    let q : QuatSphere3 := ⟨jQuat, by simpa [dist_zero_right, Metric.mem_sphere] using h_j_norm⟩
    have h9 : jQuat * iQuat * star jQuat = -iQuat := by
      apply QuaternionAlgebra.ext <;> simp [jQuat, iQuat]
    have h_main : jQuat * iQuat * star jQuat = vq := by rw [h9, h_case]
    have h_eq : hopfMap q = v := by apply Subtype.ext; exact h_main
    exact ⟨q, h_eq⟩
  · have h_ne : iQuat + vq ≠ 0 := by
      intro h
      have h' : vq = -iQuat := by
        calc vq = iQuat + vq - iQuat := by abel
             _ = 0 - iQuat := by rw [h]
             _ = -iQuat := by simp
      exact h_case h'
    set w : ℍ := iQuat + vq with hw_def
    have hw_norm_pos : 0 < ‖w‖ := norm_pos_iff.mpr h_ne
    set q0 : ℍ := (1 / ‖w‖) • w with hq0_def
    have h_q0_norm : ‖q0‖ = 1 := by
      have h_pos : 0 < (1 / ‖w‖) := by positivity
      have h : ‖q0‖ = |(1 / ‖w‖)| * ‖w‖ := by simpa [hq0_def] using norm_smul (1 / ‖w‖) w
      rw [h, abs_of_pos h_pos] <;> field_simp [hw_norm_pos.ne']
    let q : QuatSphere3 := ⟨q0, by simpa [dist_zero_right, Metric.mem_sphere] using h_q0_norm⟩
    have h_star_v : star vq = -vq := by
      have h1 : star vq = -vq ↔ vq.re = 0 := star_eq_neg
      exact h1.mpr hv_re
    have h_star_w : star w = -w := by
      rw [show star w = star (iQuat + vq) from rfl, star_add, star_iQuat, h_star_v] <;> simp [hw_def] <;> abel
    have h_key : w * iQuat * star w = normSq w • vq := by
      rw [h_star_w]
      have h1 : w * iQuat * (-w) = -(w * iQuat * w) := by simp [mul_neg]
      rw [h1]
      have h2 : w * iQuat * w = -normSq w • vq := by
        set a := vq.imI with ha
        set b := vq.imJ with hb
        set c := vq.imK with hc
        have h_abc : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
          have h : normSq vq = a ^ 2 + b ^ 2 + c ^ 2 := by simp [normSq_def', hv_re, ha, hb, hc]
          rw [h] at hv_normSq <;> exact hv_normSq
        have hw_re : w.re = 0 := by simp [w, iQuat, hv_re]
        have hw_imI : w.imI = 1 + a := by simp [w, iQuat, ha]
        have hw_imJ : w.imJ = b := by simp [w, iQuat, hb]
        have hw_imK : w.imK = c := by simp [w, iQuat, hc]
        have h_normSq_w : normSq w = 2 * (1 + a) := by
          have h : normSq w = w.re ^ 2 + w.imI ^ 2 + w.imJ ^ 2 + w.imK ^ 2 := by simp [normSq_def']
          rw [h, hw_re, hw_imI, hw_imJ, hw_imK] <;> nlinarith
        apply QuaternionAlgebra.ext <;> simp [hw_re, hw_imI, hw_imJ, hw_imK, iQuat, hv_re, ha, hb, hc, h_normSq_w] <;> ring_nf <;> nlinarith
      rw [h2] <;> simp
    have h_star_q0 : star q0 = (1 / ‖w‖) • star w := by
      have h : star ((1 / ‖w‖) • w) = (1 / ‖w‖) • star w := Quaternion.star_smul (1 / ‖w‖) w
      exact h
    have h31 : ((1 / ‖w‖) • w) * iQuat = (1 / ‖w‖) • (w * iQuat) := by rw [smul_mul_assoc]
    have h_step : ∀ (r s : ℝ) (x y : ℍ), (r • x) * (s • y) = (r * s) • (x * y) := by
      intro r s x y
      calc (r • x) * (s • y) = r • (x * (s • y)) := by rw [smul_mul_assoc]
        _ = r • (s • (x * y)) := by have h4 : x * (s • y) = s • (x * y) := mul_smul_comm s x y; rw [h4]
        _ = (r * s) • (x * y) := by rw [smul_smul]
    have h_main : q0 * iQuat * star q0 = vq := by
      rw [hq0_def, h_star_q0]
      have h3 : ((1 / ‖w‖) • w) * iQuat * ((1 / ‖w‖) • star w)
               = ((1 / ‖w‖) * (1 / ‖w‖)) • (w * iQuat * star w) := by
        calc
          ((1 / ‖w‖) • w) * iQuat * ((1 / ‖w‖) • star w)
            = ((1 / ‖w‖) • (w * iQuat)) * ((1 / ‖w‖) • star w) := by rw [h31]
          _ = ((1 / ‖w‖) * (1 / ‖w‖)) • ((w * iQuat) * star w) := h_step (1 / ‖w‖) (1 / ‖w‖) (w * iQuat) (star w)
          _ = ((1 / ‖w‖) * (1 / ‖w‖)) • (w * iQuat * star w) := by rfl
      rw [h3, h_key]
      have h4 : ((1 / ‖w‖) * (1 / ‖w‖)) • (normSq w • vq)
               = ((1 / ‖w‖) * (1 / ‖w‖) * normSq w) • vq := by rw [smul_smul]
      rw [h4]
      have h5 : (1 / ‖w‖) * (1 / ‖w‖) * normSq w = 1 := by
        have h6 : normSq w = ‖w‖ * ‖w‖ := by rw [normSq_eq_norm_mul_self]
        rw [h6] <;> field_simp [hw_norm_pos.ne']
      rw [h5] <;> simp
    have h_eq : hopfMap q = v := by apply Subtype.ext; exact h_main
    exact ⟨q, h_eq⟩

/-! ## Commutator identity -/

theorem comm_i_iff_imJ_imK_zero (q : ℍ) :
    q * iQuat = iQuat * q ↔ q.imJ = 0 ∧ q.imK = 0 := by
  set a := q.re with ha
  set b := q.imI with hb
  set c := q.imJ with hc
  set d := q.imK with hd
  have hq : q = ⟨a, b, c, d⟩ := by
    exact ext q { re := a, imI := b, imJ := c, imK := d } ha hb hc hd
  constructor
  · intro h
    have h_imJ : (q * iQuat).imJ = (iQuat * q).imJ := by rw [h]
    have h_imK : (q * iQuat).imK = (iQuat * q).imK := by rw [h]
    simp [hq, iQuat] at h_imJ h_imK <;> exact ⟨by linarith, by linarith⟩
  · rintro ⟨hJ, hK⟩
    rw [hq]
    apply QuaternionAlgebra.ext <;> simp [iQuat, hJ, hK]

theorem hopfMap_eq_i_iff_comm (q : QuatSphere3) :
    hopfMap q = iQuatSphere2 ↔ (q.val * iQuat = iQuat * q.val) := by
  have h_norm : ‖(q : ℍ)‖ = 1 := sphere3_norm_eq_one q
  have h_normSq : normSq (q : ℍ) = 1 := by
    rw [normSq_eq_norm_mul_self, h_norm] <;> ring
  have h_star_mul : star (q : ℍ) * (q : ℍ) = (1 : ℍ) := by
    have h : star (q : ℍ) * (q : ℍ) = ↑(normSq (q : ℍ)) := star_mul_self (q : ℍ)
    rw [h, h_normSq] <;> simp
  have h_mul_star : (q : ℍ) * star (q : ℍ) = (1 : ℍ) := by
    have h : (q : ℍ) * star (q : ℍ) = ↑(normSq (q : ℍ)) := self_mul_star (q : ℍ)
    rw [h, h_normSq] <;> simp
  constructor
  · intro h
    have h₁ : (q : ℍ) * iQuat * star (q : ℍ) = iQuat := by exact_mod_cast (congr_arg Subtype.val h)
    have h₂ : (q : ℍ) * iQuat * star (q : ℍ) * (q : ℍ) = iQuat * (q : ℍ) := by rw [h₁]
    have h₃ : (q : ℍ) * iQuat * (star (q : ℍ) * (q : ℍ)) = iQuat * (q : ℍ) := by rwa [mul_assoc] at h₂
    rw [h_star_mul] at h₃
    simpa using h₃
  · intro h
    have h₁ : (q : ℍ) * iQuat * star (q : ℍ) = iQuat := by
      calc (q : ℍ) * iQuat * star (q : ℍ)
          = iQuat * (q : ℍ) * star (q : ℍ) := by rw [h]
        _ = iQuat * ((q : ℍ) * star (q : ℍ)) := by rw [mul_assoc]
        _ = iQuat * (1 : ℍ) := by rw [h_mul_star]
        _ = iQuat := by simp
    apply Subtype.ext
    exact h₁

/-! ## Left multiplication isometry -/

noncomputable def leftMul (q0 : QuatSphere3) (q : QuatSphere3) : QuatSphere3 :=
  let q1 : ℍ := q0.val * q.val
  have h_norm : ‖q1‖ = 1 := by
    rw [norm_mul, sphere3_norm_eq_one q0, sphere3_norm_eq_one q] <;> ring
  ⟨q1, by simpa [dist_zero_right, Metric.mem_sphere] using h_norm⟩

theorem leftMul_norm_diff (q0 q1 q2 : QuatSphere3) :
    ‖(leftMul q0 q1).val - (leftMul q0 q2).val‖ = ‖q1.val - q2.val‖ := by
  have h2 : (leftMul q0 q1).val - (leftMul q0 q2).val = q0.val * (q1.val - q2.val) := by
    simp [leftMul, mul_sub] <;> ring
  rw [h2, norm_mul, sphere3_norm_eq_one q0] <;> ring

theorem hopfMap_leftMul (q0 q : QuatSphere3) :
    (hopfMap (leftMul q0 q)).val = q0.val * (hopfMap q).val * star q0.val := by
  have h2 : (leftMul q0 q).val = q0.val * q.val := by rfl
  have h4 : star (q0.val * q.val) = star q.val * star q0.val := star_mul q0.val q.val
  calc
    (hopfMap (leftMul q0 q)).val
      = (leftMul q0 q).val * iQuat * star (leftMul q0 q).val := by rfl
    _ = (q0.val * q.val) * iQuat * star (q0.val * q.val) := by rw [h2]
    _ = (q0.val * q.val) * iQuat * (star q.val * star q0.val) := by rw [h4]
    _ = q0.val * (q.val * iQuat * star q.val) * star q0.val := by
      simp [mul_assoc] <;> rfl
    _ = q0.val * (hopfMap q).val * star q0.val := by rfl

/-! ## Norm squared helper -/

lemma quat_normSq_eq (x : ℍ) : ‖x‖ ^ 2 = x.re ^ 2 + x.imI ^ 2 + x.imJ ^ 2 + x.imK ^ 2 := by
  have h : ‖x‖ ^ 2 = normSq x := by rw [normSq_eq_norm_mul_self, pow_two]
  rw [h]
  simp [normSq_def'] <;> ring

/-! ## Key distance bound for fiber over i -/

theorem hopfMap_minus_i_norm (q : QuatSphere3) :
    ‖(hopfMap q).val - iQuat‖ = 2 * Real.sqrt (q.val.imJ ^ 2 + q.val.imK ^ 2) := by
  have h_normSq : normSq q.val = 1 := by
    rw [normSq_eq_norm_mul_self, sphere3_norm_eq_one q] <;> ring
  have h_mul_star : q.val * star q.val = (1 : ℍ) := by
    have h : q.val * star q.val = ↑(normSq q.val) := self_mul_star q.val
    rw [h, h_normSq] <;> simp
  set c := q.val.imJ with hc
  set d := q.val.imK with hd
  let comm_quat : ℍ := { re := 0, imI := 0, imJ := 2 * d, imK := -2 * c }
  have h1 : q.val * iQuat - iQuat * q.val = comm_quat := by
    set a := q.val.re with ha
    set b := q.val.imI with hb
    have hq : q.val = { re := a, imI := b, imJ := c, imK := d } := by
      exact ext q.val { re := a, imI := b, imJ := c, imK := d } ha hb hc hd
    rw [hq]
    apply QuaternionAlgebra.ext <;> simp [iQuat, comm_quat] <;> ring
  have h_right : iQuat * (q.val * star q.val) = iQuat := by
    rw [h_mul_star] <;> simp
  have h_assoc1 : q.val * iQuat * star q.val = (q.val * iQuat) * star q.val := by rfl
  have h_assoc2 : iQuat * (q.val * star q.val) = (iQuat * q.val) * star q.val := by
    exact Eq.symm (mul_assoc iQuat (↑q) (star ↑q))
  have h_goal : (hopfMap q).val - iQuat = (q.val * iQuat - iQuat * q.val) * star q.val := by
    have h_eq1 : (hopfMap q).val = q.val * iQuat * star q.val := by rfl
    have h_step1 : q.val * iQuat * star q.val - iQuat = q.val * iQuat * star q.val - iQuat * (q.val * star q.val) := by
      exact congr_arg (fun x => q.val * iQuat * star q.val - x) h_right.symm
    calc
      (hopfMap q).val - iQuat
        = q.val * iQuat * star q.val - iQuat := by rw [h_eq1]
      _ = q.val * iQuat * star q.val - iQuat * (q.val * star q.val) := h_step1
      _ = (q.val * iQuat) * star q.val - (iQuat * q.val) * star q.val := by rw [h_assoc1, h_assoc2]
      _ = (q.val * iQuat - iQuat * q.val) * star q.val := by rw [←sub_mul]
  have h_main : (hopfMap q).val - iQuat = comm_quat * star q.val := by
    rw [h_goal, h1]
  rw [h_main]
  have h2 : ‖comm_quat * star q.val‖ = ‖comm_quat‖ := by
    rw [norm_mul, Quaternion.norm_star, sphere3_norm_eq_one q] <;> ring
  rw [h2]
  have h3 : ‖comm_quat‖ ^ 2 = 4 * (c ^ 2 + d ^ 2) := by
    rw [quat_normSq_eq] <;> simp [comm_quat] <;> ring
  have h4 : 0 ≤ ‖comm_quat‖ := by positivity
  have h5 : ‖comm_quat‖ = 2 * Real.sqrt (c ^ 2 + d ^ 2) := by
    nlinarith [Real.sqrt_nonneg (c ^ 2 + d ^ 2), Real.sq_sqrt (show 0 ≤ c ^ 2 + d ^ 2 by positivity)]
  exact h5

/-- Algebraic inequality: (√(1-x) - 1)² ≤ x for 0 ≤ x ≤ 1. -/
lemma sqrt_ineq (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (Real.sqrt (1 - x) - 1) ^ 2 ≤ x := by
  have h2 : 0 ≤ 1 - x := by linarith
  have h3 : Real.sqrt (1 - x) ≤ 1 := by
    have h4 : Real.sqrt (1 - x) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
    have h5 : Real.sqrt 1 = 1 := Real.sqrt_one
    rw [h5] at h4
    exact h4
  have h6 : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt h2]

/-- For any q, exists p in F_i with ‖q.val - p.val‖ ≤ (1/√2) * ‖hopfMap(q) - i‖. -/
theorem exists_close_to_fiber_i (q : QuatSphere3) :
    ∃ (p : QuatSphere3), p ∈ fiber iQuatSphere2 ∧
      ‖q.val - p.val‖ ≤ (1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖ := by
  set a := q.val.re with ha
  set b := q.val.imI with hb
  set c := q.val.imJ with hc
  set d := q.val.imK with hd
  set x : ℝ := c ^ 2 + d ^ 2 with hx
  have hx_nonneg : 0 ≤ x := by positivity
  have hx_le_one : x ≤ 1 := by
    have h1 : ‖q.val‖ = 1 := sphere3_norm_eq_one q
    have h2 : ‖q.val‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := quat_normSq_eq q.val
    have h7 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
      rw [←h2, h1] <;> ring
    nlinarith [sq_nonneg a, sq_nonneg b, hx]
  set z : ℝ := Real.sqrt (a ^ 2 + b ^ 2) with hz
  have hz_nonneg : 0 ≤ z := by positivity
  have hz2 : z ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hz, Real.sq_sqrt] <;> positivity
  have h_z2_x : z ^ 2 + x = 1 := by
    have h1 : ‖q.val‖ = 1 := sphere3_norm_eq_one q
    have h2 : ‖q.val‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := quat_normSq_eq q.val
    have h7 : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1 := by
      rw [←h2, h1] <;> ring
    linarith [hz2, hx, h7]
  by_cases hz_pos : 0 < z
  · -- Case z > 0
    let ab_quat : ℍ := { re := a, imI := b, imJ := 0, imK := 0 }
    let p_val : ℍ := (1 / z) • ab_quat
    have hp_norm : ‖p_val‖ = 1 := by
      have h2 : ‖ab_quat‖ = z := by
        have h3 : ‖ab_quat‖ ^ 2 = a ^ 2 + b ^ 2 := by
          rw [quat_normSq_eq] <;> simp [ab_quat] <;> ring
        have h4 : ‖ab_quat‖ ^ 2 = z ^ 2 := by
          rw [h3, ←hz2]
        have h5 : 0 ≤ ‖ab_quat‖ := by positivity
        have h6 : Real.sqrt (‖ab_quat‖ ^ 2) = Real.sqrt (z ^ 2) := by rw [h4]
        have h7 : Real.sqrt (‖ab_quat‖ ^ 2) = ‖ab_quat‖ := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h5]
        have h8 : Real.sqrt (z ^ 2) = z := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hz_nonneg]
        rw [h7, h8] at h6
        exact h6
      have h_smul : p_val = (1 / z) • ab_quat := by rfl
      have h_pos : 0 < (1 / z) := by positivity
      have h_norm_smul : ‖p_val‖ = (1 / z) * ‖ab_quat‖ := by
        have h1 : ‖(1 / z) • ab_quat‖ = ‖(1 / z : ℝ)‖ * ‖ab_quat‖ := norm_smul (1 / z) ab_quat
        have h2real : ‖(1 / z : ℝ)‖ = (1 / z) := by
          rw [Real.norm_eq_abs, abs_of_pos h_pos]
        have h3 : ‖p_val‖ = ‖(1 / z) • ab_quat‖ := by rfl
        rw [h3, h1, h2real]
      rw [h_norm_smul, h2] <;> field_simp [hz_pos.ne'] <;> ring
    let p : QuatSphere3 := ⟨p_val, by simpa [dist_zero_right, Metric.mem_sphere] using hp_norm⟩
    have h_p_comm : p_val * iQuat = iQuat * p_val := by
      have h_imJ : p_val.imJ = 0 := by simp [p_val, ab_quat] <;> norm_num
      have h_imK : p_val.imK = 0 := by simp [p_val, ab_quat] <;> norm_num
      exact (comm_i_iff_imJ_imK_zero p_val).mpr ⟨h_imJ, h_imK⟩
    have h_p_fiber : p ∈ fiber iQuatSphere2 := by
      simp only [fiber, Set.mem_setOf_eq]
      exact (hopfMap_eq_i_iff_comm p).mpr h_p_comm
    let diff_quat : ℍ := { re := a - a / z, imI := b - b / z, imJ := c, imK := d }
    have h_diff : q.val - p_val = diff_quat := by
      simp [p_val, ab_quat, diff_quat] <;> apply QuaternionAlgebra.ext <;> simp <;> ring
    have h_dist2 : ‖q.val - p_val‖ ^ 2 = (a - a / z) ^ 2 + (b - b / z) ^ 2 + c ^ 2 + d ^ 2 := by
      rw [h_diff, quat_normSq_eq] <;> simp [diff_quat] <;> ring
    have h4 : (a - a / z) ^ 2 + (b - b / z) ^ 2 = (z - 1) ^ 2 := by
      have h5 : a - a / z = a * (1 - 1 / z) := by ring
      have h6 : b - b / z = b * (1 - 1 / z) := by ring
      rw [h5, h6]
      have h7 : (a * (1 - 1 / z)) ^ 2 + (b * (1 - 1 / z)) ^ 2 = (a ^ 2 + b ^ 2) * (1 - 1 / z) ^ 2 := by ring
      rw [h7, ←hz2]
      have h8 : z ^ 2 * (1 - 1 / z) ^ 2 = (z - 1) ^ 2 := by
        field_simp [hz_pos.ne'] <;> ring
      exact h8
    have h_dist2' : ‖q.val - p_val‖ ^ 2 = (z - 1) ^ 2 + x := by
      rw [h_dist2, h4] <;> ring
    have h_z_eq : z = Real.sqrt (1 - x) := by
      have h9 : z ^ 2 = 1 - x := by linarith
      have h10 : 0 ≤ 1 - x := by linarith
      have h11 : 0 ≤ z := hz_nonneg
      have h12 : Real.sqrt (z ^ 2) = z := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h11]
      have h13 : Real.sqrt (z ^ 2) = Real.sqrt (1 - x) := by rw [h9]
      exact h12.symm.trans h13
    have h10 : (z - 1) ^ 2 ≤ x := by
      simpa [h_z_eq] using sqrt_ineq x hx_nonneg hx_le_one
    have h11 : ‖q.val - p_val‖ ^ 2 ≤ 2 * x := by
      rw [h_dist2'] <;> linarith
    have hx' : q.val.imJ ^ 2 + q.val.imK ^ 2 = x := by
      have h : q.val.imJ ^ 2 + q.val.imK ^ 2 = c ^ 2 + d ^ 2 := by
        rw [hc.symm, hd.symm] <;> ring
      rw [h] <;> ring
    have h12 : ‖(hopfMap q).val - iQuat‖ ^ 2 = 4 * x := by
      rw [hopfMap_minus_i_norm q, hx']
      have h_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_nonneg
      have h_goal : (2 * Real.sqrt x) ^ 2 = 4 * x := by
        have h1 : (2 * Real.sqrt x) ^ 2 = 4 * (Real.sqrt x) ^ 2 := by ring
        rw [h1, h_sq] <;> ring
      exact h_goal
    have h13 : 0 ≤ ‖q.val - p_val‖ := by positivity
    have h14 : 0 ≤ (1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖ := by positivity
    have h15 : ((1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖) ^ 2 = 2 * x := by
      have h16 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
        have h17 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        field_simp [h17.ne'] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h_expand : ((1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖) ^ 2 = (1 / Real.sqrt 2) ^ 2 * ‖(hopfMap q).val - iQuat‖ ^ 2 := by ring
      rw [h_expand, h16, h12] <;> ring
    have h16 : ‖q.val - p.val‖ ≤ (1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖ := by
      nlinarith
    exact ⟨p, h_p_fiber, h16⟩
  · -- Case z = 0
    have hz0 : z = 0 := by linarith
    have hab : a ^ 2 + b ^ 2 = 0 := by
      have h : z ^ 2 = 0 := by rw [hz0] <;> ring
      rw [hz2] at h
      exact h
    have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    have hx1 : x = 1 := by linarith
    let p_val : ℍ := 1
    have hp_norm : ‖p_val‖ = 1 := by simp [p_val]
    let p : QuatSphere3 := ⟨p_val, by simpa [dist_zero_right, Metric.mem_sphere] using hp_norm⟩
    have h_p_comm : p_val * iQuat = iQuat * p_val := by
      have h_imJ : p_val.imJ = 0 := by simp [p_val] <;> norm_num
      have h_imK : p_val.imK = 0 := by simp [p_val] <;> norm_num
      exact (comm_i_iff_imJ_imK_zero p_val).mpr ⟨h_imJ, h_imK⟩
    have h_p_fiber : p ∈ fiber iQuatSphere2 := by
      simp only [fiber, Set.mem_setOf_eq]
      exact (hopfMap_eq_i_iff_comm p).mpr h_p_comm
    have hq : q.val = { re := a, imI := b, imJ := c, imK := d } := by
      exact ext q.val { re := a, imI := b, imJ := c, imK := d } ha hb hc hd
    let diff_quat2 : ℍ := { re := -1, imI := 0, imJ := c, imK := d }
    have h_diff : q.val - p_val = diff_quat2 := by
      rw [hq, ha0, hb0] <;> simp [p_val, diff_quat2] <;> apply QuaternionAlgebra.ext <;> simp <;> ring
    have h_dist2 : ‖q.val - p_val‖ ^ 2 = 2 := by
      have h1 : ‖q.val - p_val‖ = ‖diff_quat2‖ := by rw [h_diff]
      rw [h1]
      have h2 : ‖diff_quat2‖ ^ 2 = (-1 : ℝ)^2 + (0 : ℝ)^2 + c^2 + d^2 := by
        rw [quat_normSq_eq diff_quat2] <;> simp [diff_quat2] <;> ring
      rw [h2]
      have h3 : c^2 + d^2 = x := hx.symm
      have h_goal : (-1 : ℝ)^2 + (0 : ℝ)^2 + c^2 + d^2 = 1 + (c^2 + d^2) := by ring
      rw [h_goal, h3, hx1] <;> norm_num
    have hx' : q.val.imJ ^ 2 + q.val.imK ^ 2 = x := by
      have h : q.val.imJ ^ 2 + q.val.imK ^ 2 = c ^ 2 + d ^ 2 := by
        rw [hc.symm, hd.symm] <;> ring
      rw [h] <;> ring
    have h12 : ‖(hopfMap q).val - iQuat‖ ^ 2 = 4 := by
      rw [hopfMap_minus_i_norm q, hx']
      have h_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx_nonneg
      have h_x1 : x = 1 := hx1
      have h_goal : (2 * Real.sqrt x) ^ 2 = 4 := by
        have h1 : (2 * Real.sqrt x) ^ 2 = 4 * (Real.sqrt x) ^ 2 := by ring
        rw [h1, h_sq, h_x1] <;> norm_num
      exact h_goal
    have h13 : 0 ≤ ‖q.val - p_val‖ := by positivity
    have h14 : ((1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖) ^ 2 = 2 := by
      have h15 : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
        have h16 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        field_simp [h16.ne'] <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h_expand : ((1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖) ^ 2 = (1 / Real.sqrt 2) ^ 2 * ‖(hopfMap q).val - iQuat‖ ^ 2 := by ring
      rw [h_expand, h15, h12] <;> ring
    have h17 : ‖q.val - p_val‖ ≤ (1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖ := by
      set b := (1 / Real.sqrt 2) * ‖(hopfMap q).val - iQuat‖ with hb_def
      have h18 : ‖q.val - p_val‖ ^ 2 = b ^ 2 := by
        rw [h_dist2, h14]
      have h19 : 0 ≤ ‖q.val - p_val‖ := h13
      have h20 : 0 ≤ b := by positivity
      have h21 : (‖q.val - p_val‖ - b) * (‖q.val - p_val‖ + b) = 0 := by linarith
      by_cases h_sum : ‖q.val - p_val‖ + b = 0
      · have h_a0 : ‖q.val - p_val‖ = 0 := by linarith
        have h_b0 : b = 0 := by linarith
        rw [h_a0, h_b0] <;> norm_num
      · have h_sum_pos : 0 < ‖q.val - p_val‖ + b := by
          exact lt_of_le_of_ne (by positivity) (Ne.symm h_sum)
        have h_sub : ‖q.val - p_val‖ - b = 0 := by
          exact (mul_eq_zero.mp h21).resolve_right h_sum_pos.ne'
        have h_eq : ‖q.val - p_val‖ = b := by linarith
        rw [h_eq]
    exact ⟨p, h_p_fiber, h17⟩

/-- Distance bound for arbitrary fiber. -/
theorem exists_close_to_fiber (v : QuatSphere2) (q : QuatSphere3) :
    ∃ (p : QuatSphere3), p ∈ fiber v ∧
      ‖q.val - p.val‖ ≤ (1 / Real.sqrt 2) * ‖(hopfMap q).val - v.val‖ := by
  have h_surj : ∃ (q0 : QuatSphere3), hopfMap q0 = v := hopfMap_surjective v
  rcases h_surj with ⟨q0, hq0⟩
  let q0_inv_val : ℍ := star q0.val
  have hq0_inv_norm : ‖q0_inv_val‖ = 1 := by
    rw [Quaternion.norm_star, sphere3_norm_eq_one q0]
  let q0_inv : QuatSphere3 := ⟨q0_inv_val, by simpa [dist_zero_right, Metric.mem_sphere] using hq0_inv_norm⟩
  let q' := leftMul q0_inv q
  have h_normSq0 : normSq q0.val = 1 := by
    rw [normSq_eq_norm_mul_self, sphere3_norm_eq_one q0] <;> ring
  have h_mul_star0 : q0.val * star q0.val = (1 : ℍ) := by
    have h : q0.val * star q0.val = ↑(normSq q0.val) := self_mul_star q0.val
    rw [h, h_normSq0] <;> simp
  have h1 : (leftMul q0 q').val = q.val := by
    have h2 : (leftMul q0 q').val = q0.val * (q0_inv_val * q.val) := by
      simp [leftMul, q', q0_inv] <;> ring
    rw [h2]
    have h3 : q0.val * (q0_inv_val * q.val) = q.val := by
      rw [←mul_assoc, h_mul_star0, one_mul]
    exact h3
  have h2 := exists_close_to_fiber_i q'
  rcases h2 with ⟨p', hp'_fiber, hp'_dist⟩
  let p := leftMul q0 p'
  have hp_fiber : p ∈ fiber v := by
    simp only [fiber, Set.mem_setOf_eq]
    have h3 : (hopfMap p).val = v.val := by
      have h4 : (hopfMap p).val = q0.val * (hopfMap p').val * star q0.val := hopfMap_leftMul q0 p'
      rw [h4]
      have h5 : (hopfMap p').val = iQuat := by
        have h6 : hopfMap p' = iQuatSphere2 := hp'_fiber
        exact congr_arg Subtype.val h6
      rw [h5]
      have h7 : q0.val * iQuat * star q0.val = v.val := by
        have h_def : (hopfMap q0).val = q0.val * iQuat * star q0.val := by rfl
        have h9 : (hopfMap q0).val = v.val := congr_arg Subtype.val hq0
        rw [h_def] at h9
        exact h9
      exact h7
    have h8 : hopfMap p = v := by
      apply Subtype.ext
      exact h3
    exact h8
  have h4 : ‖q.val - p.val‖ = ‖q'.val - p'.val‖ := by
    have h5 : q.val = (leftMul q0 q').val := h1.symm
    have h6 : p.val = (leftMul q0 p').val := by rfl
    rw [h5, h6]
    exact leftMul_norm_diff q0 q' p'
  have h5 : ‖(hopfMap q).val - v.val‖ = ‖(hopfMap q').val - iQuat‖ := by
    have hq_eq : q = leftMul q0 q' := by
      apply Subtype.ext
      exact h1.symm
    have h7 : (hopfMap (leftMul q0 q')).val = q0.val * (hopfMap q').val * star q0.val :=
      hopfMap_leftMul q0 q'
    have h8 : v.val = q0.val * iQuat * star q0.val := by
      have h9 : (hopfMap q0).val = v.val := congr_arg Subtype.val hq0
      have h10 : (hopfMap q0).val = q0.val * iQuat * star q0.val := by rfl
      rw [h10] at h9
      exact h9.symm
    have h_factor : q0.val * (hopfMap q').val * star q0.val - q0.val * iQuat * star q0.val =
        q0.val * ((hopfMap q').val - iQuat) * star q0.val := by
      have h1 : (q0.val * (hopfMap q').val) * star q0.val - (q0.val * iQuat) * star q0.val =
          (q0.val * (hopfMap q').val - q0.val * iQuat) * star q0.val := by
        rw [←sub_mul]
      have h2 : q0.val * (hopfMap q').val - q0.val * iQuat = q0.val * ((hopfMap q').val - iQuat) := by
        rw [←mul_sub]
      calc
        q0.val * (hopfMap q').val * star q0.val - q0.val * iQuat * star q0.val
          = (q0.val * (hopfMap q').val - q0.val * iQuat) * star q0.val := h1
      _ = (q0.val * ((hopfMap q').val - iQuat)) * star q0.val := by rw [h2]
      _ = q0.val * ((hopfMap q').val - iQuat) * star q0.val := by rfl
    calc
      ‖(hopfMap q).val - v.val‖
        = ‖(hopfMap (leftMul q0 q')).val - v.val‖ := by rw [hq_eq]
      _ = ‖q0.val * (hopfMap q').val * star q0.val - q0.val * iQuat * star q0.val‖ := by rw [h7, h8]
      _ = ‖q0.val * ((hopfMap q').val - iQuat) * star q0.val‖ := by rw [h_factor]
      _ = ‖(hopfMap q').val - iQuat‖ := by
        rw [norm_mul, norm_mul, sphere3_norm_eq_one q0, Quaternion.norm_star q0.val, sphere3_norm_eq_one q0] <;> ring
  have h_final : ‖q.val - p.val‖ ≤ (1 / Real.sqrt 2) * ‖(hopfMap q).val - v.val‖ := by
    calc ‖q.val - p.val‖
        = ‖q'.val - p'.val‖ := h4
      _ ≤ (1 / Real.sqrt 2) * ‖(hopfMap q').val - iQuat‖ := hp'_dist
      _ = (1 / Real.sqrt 2) * ‖(hopfMap q).val - v.val‖ := by rw [h5]
  exact ⟨p, hp_fiber, h_final⟩

/-! ## Fiber parameterization -/

/-- Embed ℂ as quaternions with j=k=0. -/
def complexToQuat (z : ℂ) : ℍ := ⟨z.re, z.im, 0, 0⟩

theorem norm_complexToQuat (z : ℂ) : ‖complexToQuat z‖ = ‖z‖ := by
  have h1 : ‖complexToQuat z‖ ^ 2 = normSq (complexToQuat z) := by
    rw [normSq_eq_norm_mul_self, pow_two]
  have h2 : normSq (complexToQuat z) = z.re ^ 2 + z.im ^ 2 := by
    simp [complexToQuat, normSq_def']
  have h3 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq] <;> simp [Complex.normSq] <;> ring
  have h4 : ‖complexToQuat z‖ ^ 2 = ‖z‖ ^ 2 := by rw [h1, h2, h3]
  have h5 : 0 ≤ ‖complexToQuat z‖ := by positivity
  have h6 : 0 ≤ ‖z‖ := by positivity
  nlinarith

/-- Extract complex number from quaternion with imJ=imK=0. -/
def quatToComplex (q : ℍ) : ℂ := ⟨q.re, q.imI⟩

theorem complexToQuat_quatToComplex (q : ℍ) (hJ : q.imJ = 0) (hK : q.imK = 0) :
    complexToQuat (quatToComplex q) = q := by
  apply QuaternionAlgebra.ext <;> simp [complexToQuat, quatToComplex, hJ, hK]

abbrev Circle1 : Type := Metric.sphere (0 : ℂ) 1

/-- Parameterize fiber over i by Circle1. -/
noncomputable def fiberIParam (z : Circle1) : QuatSphere3 :=
  let q0 : ℍ := complexToQuat z.val
  have h_norm : ‖q0‖ = 1 := by
    rw [norm_complexToQuat]
    have hz : ‖z.val‖ = 1 := by
      have hz0 : dist z.val 0 = 1 := z.property
      rw [dist_zero_right] at hz0
      exact hz0
    exact hz
  ⟨q0, by simpa [dist_zero_right, Metric.mem_sphere] using h_norm⟩

theorem fiberIParam_in_fiber (z : Circle1) : fiberIParam z ∈ fiber iQuatSphere2 := by
  let q0 : ℍ := complexToQuat z.val
  have h_imJ : q0.imJ = 0 := by simp [q0, complexToQuat] <;> norm_num
  have h_imK : q0.imK = 0 := by simp [q0, complexToQuat] <;> norm_num
  have h_comm : q0 * iQuat = iQuat * q0 :=
    (comm_i_iff_imJ_imK_zero q0).mpr ⟨h_imJ, h_imK⟩
  simp only [fiber, Set.mem_setOf_eq]
  exact (hopfMap_eq_i_iff_comm (fiberIParam z)).mpr h_comm

theorem fiberIParam_isometry (z1 z2 : Circle1) :
    ‖(fiberIParam z1).val - (fiberIParam z2).val‖ = ‖z1.val - z2.val‖ := by
  have h1 : (fiberIParam z1).val - (fiberIParam z2).val = complexToQuat (z1.val - z2.val) := by
    simp [fiberIParam, complexToQuat] <;> apply QuaternionAlgebra.ext <;> simp <;> ring
  rw [h1]
  exact norm_complexToQuat (z1.val - z2.val)

theorem fiberIParam_surjective : fiber iQuatSphere2 = Set.range fiberIParam := by
  apply Set.Subset.antisymm
  · intro q hq
    have h_comm : q.val * iQuat = iQuat * q.val := (hopfMap_eq_i_iff_comm q).mp hq
    have h_imJ : q.val.imJ = 0 := (comm_i_iff_imJ_imK_zero q.val).mp h_comm |>.1
    have h_imK : q.val.imK = 0 := (comm_i_iff_imJ_imK_zero q.val).mp h_comm |>.2
    let z_complex : ℂ := quatToComplex q.val
    have h_norm : ‖z_complex‖ = 1 := by
      have h1 : ‖complexToQuat z_complex‖ = ‖z_complex‖ := norm_complexToQuat z_complex
      have h2 : complexToQuat z_complex = q.val := complexToQuat_quatToComplex q.val h_imJ h_imK
      rw [←h1, h2]
      exact sphere3_norm_eq_one q
    let z : Circle1 := ⟨z_complex, by simpa [dist_zero_right, Metric.mem_sphere] using h_norm⟩
    have h4 : (fiberIParam z).val = q.val := by
      dsimp only [fiberIParam]
      exact complexToQuat_quatToComplex q.val h_imJ h_imK
    have h3 : fiberIParam z = q := Subtype.ext h4
    exact ⟨z, h3⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact fiberIParam_in_fiber z

/-- Parameterize arbitrary fiber. -/
noncomputable def fiberParam (v : QuatSphere2) (q0 : QuatSphere3) (hq0 : hopfMap q0 = v)
    (z : Circle1) : QuatSphere3 :=
  leftMul q0 (fiberIParam z)

theorem fiberParam_in_fiber (v q0 hq0 z) : fiberParam v q0 hq0 z ∈ fiber v := by
  simp only [fiber, Set.mem_setOf_eq, fiberParam]
  have h3 : (hopfMap (leftMul q0 (fiberIParam z))).val = v.val := by
    have h4 : (hopfMap (leftMul q0 (fiberIParam z))).val =
        q0.val * (hopfMap (fiberIParam z)).val * star q0.val := hopfMap_leftMul q0 (fiberIParam z)
    rw [h4]
    have h5 : (hopfMap (fiberIParam z)).val = iQuat := by
      have h6 : hopfMap (fiberIParam z) = iQuatSphere2 := fiberIParam_in_fiber z
      exact congr_arg Subtype.val h6
    rw [h5]
    have h7 : q0.val * iQuat * star q0.val = v.val := by
      have h_def : (hopfMap q0).val = q0.val * iQuat * star q0.val := by rfl
      have h9 : (hopfMap q0).val = v.val := congr_arg Subtype.val hq0
      rw [h_def] at h9
      exact h9
    exact h7
  apply Subtype.ext
  exact h3

theorem fiberParam_isometry (v q0 hq0 z1 z2) :
    ‖(fiberParam v q0 hq0 z1).val - (fiberParam v q0 hq0 z2).val‖ = ‖z1.val - z2.val‖ := by
  simp only [fiberParam]
  have h := leftMul_norm_diff q0 (fiberIParam z1) (fiberIParam z2)
  rw [h, fiberIParam_isometry z1 z2]

theorem fiberParam_surjective (v q0 hq0) : fiber v = Set.range (fiberParam v q0 hq0) := by
  apply Set.Subset.antisymm
  · intro q hq
    let q0_inv_val : ℍ := star q0.val
    have hq0_inv_norm : ‖q0_inv_val‖ = 1 := by
      rw [Quaternion.norm_star, sphere3_norm_eq_one q0]
    let q0_inv : QuatSphere3 := ⟨q0_inv_val, by simpa [dist_zero_right, Metric.mem_sphere] using hq0_inv_norm⟩
    let q' := leftMul q0_inv q
    have h_normSq0 : normSq q0.val = 1 := by
      rw [normSq_eq_norm_mul_self, sphere3_norm_eq_one q0] <;> ring
    have h_mul_star0 : q0.val * star q0.val = (1 : ℍ) := by
      have h : q0.val * star q0.val = ↑(normSq q0.val) := self_mul_star q0.val
      rw [h, h_normSq0] <;> simp
    have h_star_mul_self : star q0.val * q0.val = (1 : ℍ) := by
      have h : star q0.val * q0.val = ↑(normSq q0.val) := star_mul_self q0.val
      rw [h, h_normSq0] <;> simp
    have h1 : (leftMul q0 q').val = q.val := by
      have h2 : (leftMul q0 q').val = q0.val * (q0_inv_val * q.val) := by
        simp [leftMul, q', q0_inv] <;> ring
      rw [h2]
      have h3 : q0.val * (q0_inv_val * q.val) = q.val := by
        rw [←mul_assoc, h_mul_star0, one_mul]
      exact h3
    have hq_val : (hopfMap q).val = v.val := congr_arg Subtype.val hq
    have h_v_def : v.val = q0.val * iQuat * star q0.val := by
      have h9 : (hopfMap q0).val = v.val := congr_arg Subtype.val hq0
      have h10 : (hopfMap q0).val = q0.val * iQuat * star q0.val := by rfl
      rw [h10] at h9
      exact h9.symm
    have h4 : (hopfMap q').val = iQuat := by
      have h_hopf : (hopfMap q').val = q0_inv.val * (hopfMap q).val * star q0_inv.val :=
        hopfMap_leftMul q0_inv q
      rw [h_hopf]
      have h5 : q0_inv.val = star q0.val := by rfl
      have h6 : star q0_inv.val = q0.val := by
        simp [q0_inv, q0_inv_val] <;> rw [star_star]
      rw [h5, h6, hq_val, h_v_def]
      have h7 : star q0.val * (q0.val * iQuat * star q0.val) * q0.val = iQuat := by
        have h_assoc : star q0.val * (q0.val * iQuat * star q0.val) * q0.val =
            (star q0.val * q0.val) * iQuat * (star q0.val * q0.val) := by
          simp [mul_assoc]
        rw [h_assoc, h_star_mul_self] <;> simp
      exact h7
    have hq'_fiber : q' ∈ fiber iQuatSphere2 := by
      simp only [fiber, Set.mem_setOf_eq]
      apply Subtype.ext
      exact h4
    have h9 : q' ∈ Set.range fiberIParam := by
      rw [←fiberIParam_surjective]
      exact hq'_fiber
    rcases h9 with ⟨z, hz⟩
    have h10 : fiberParam v q0 hq0 z = q := by
      simp only [fiberParam]
      apply Subtype.ext
      have h11 : (leftMul q0 (fiberIParam z)).val = q.val := by
        rw [hz]
        exact h1
      exact h11
    exact ⟨z, h10⟩
  · intro y hy
    rcases hy with ⟨z, rfl⟩
    exact fiberParam_in_fiber v q0 hq0 z

/-! ## Circle covering (adapted from dune) -/

/-- Cover the unit circle by N = ⌈2π/α⌉ balls of radius α. -/
lemma circle_cover_by_balls {α : ℝ} (hα : 0 < α) :
    ∃ (s : Finset Circle1),
      (Set.univ : Set Circle1) ⊆ ⋃ x ∈ s, ball x α ∧
      s.card ≤ Nat.ceil (2 * Real.pi / α) := by
  let N : ℕ := Nat.ceil (2 * Real.pi / α)
  have hN_pos : 0 < N := by
    have h1 : 0 < 2 * Real.pi / α := by positivity
    have h2 : 0 < Nat.ceil (2 * Real.pi / α) := Nat.ceil_pos.mpr h1
    exact h2
  have hN : (2 * Real.pi / α : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
  let f : ℕ → Circle1 := fun k =>
    let z : ℂ := exp (I * (2 * Real.pi * (k : ℝ) / (N : ℝ)))
    ⟨z, by
      have h_norm : ‖z‖ = 1 := by
        rw [Complex.norm_exp] <;> simp [Complex.mul_re] <;> norm_num
      have h_dist : dist z 0 = 1 := by rw [dist_zero_right, h_norm]
      exact h_dist⟩
  let s : Finset Circle1 := image f (range N)
  have h_card : s.card ≤ N := by
    have h : s.card ≤ (range N).card := Finset.card_image_le
    simpa [s, card_range] using h
  have h_main : ∀ (z : Circle1), ∃ k ∈ range N, z ∈ ball (f k) α := by
    intro z
    have hz1 : ‖(z : ℂ)‖ = 1 := by
      have h : dist (z : ℂ) 0 = 1 := z.property
      rw [dist_zero_right] at h
      exact h
    let θ : ℝ := arg (z : ℂ)
    have hz_eq : (z : ℂ) = exp (I * θ) := by
      have h1 : (‖(z : ℂ)‖ : ℂ) * (cos θ + sin θ * I) = (z : ℂ) :=
        Complex.norm_mul_cos_add_sin_mul_I (z : ℂ)
      have h2 : (‖(z : ℂ)‖ : ℂ) = 1 := by exact_mod_cast hz1
      have h3 : cos θ + sin θ * I = (z : ℂ) := by
        rw [h2] at h1 <;> simpa using h1
      have h4 : exp (I * θ) = cos θ + sin θ * I := by
        have h5 : exp (θ * I) = cos θ + sin θ * I := Complex.exp_mul_I θ
        have h6 : I * θ = θ * I := by ring
        rw [h6] at *
        exact h5
      exact h3.symm.trans h4.symm
    have hθ_neg : -Real.pi < θ := neg_pi_lt_arg (z : ℂ)
    have hθ_le : θ ≤ Real.pi := arg_le_pi (z : ℂ)
    let θ' : ℝ := if θ < 0 then θ + 2 * Real.pi else θ
    have hθ'_nonneg : 0 ≤ θ' := by
      dsimp only [θ']; split_ifs with h <;> linarith [Real.pi_pos]
    have hθ'_lt : θ' < 2 * Real.pi := by
      dsimp only [θ']; split_ifs with h <;> linarith [Real.pi_pos]
    have h_exp_eq : exp (I * θ') = exp (I * θ) := by
      dsimp only [θ']
      split_ifs with h
      · have h5 : exp (I * (θ + 2 * Real.pi)) = exp (I * θ) := by
          have h_eq : I * (θ + 2 * Real.pi) = I * θ + I * (2 * Real.pi) := by
            simp [mul_add] <;> ring
          rw [h_eq, Complex.exp_add]
          have h6 : exp (I * (2 * Real.pi)) = 1 := by
            have h7 : I * (2 * Real.pi) = (2 * Real.pi) * I := by ring
            rw [h7, Complex.exp_mul_I] <;> norm_num
          rw [h6] <;> ring
        simpa [add_mul] using h5
      · rfl
    have h_nonneg : 0 ≤ (N : ℝ) * θ' / (2 * Real.pi) := by positivity
    let k : ℕ := Nat.floor ((N : ℝ) * θ' / (2 * Real.pi))
    have hk_lt_N : k < N := by
      have h1 : (N : ℝ) * θ' / (2 * Real.pi) < (N : ℝ) := by
        have h2 : θ' < 2 * Real.pi := hθ'_lt
        have h3 : 0 < (N : ℝ) := by exact_mod_cast hN_pos
        have h4 : 0 < 2 * Real.pi := by positivity
        have h5 : (N : ℝ) * θ' < (N : ℝ) * (2 * Real.pi) := by gcongr
        have h6 : (N : ℝ) * θ' / (2 * Real.pi) < (N : ℝ) := by
          calc (N : ℝ) * θ' / (2 * Real.pi)
              < (N : ℝ) * (2 * Real.pi) / (2 * Real.pi) := by gcongr
            _ = (N : ℝ) := by field_simp [h4.ne'] <;> ring
        exact h6
      have h5 : (k : ℝ) < (N : ℝ) := by
        have h6 : (k : ℝ) ≤ (N : ℝ) * θ' / (2 * Real.pi) := Nat.floor_le h_nonneg
        linarith
      exact_mod_cast h5
    have hk1 : (k : ℝ) ≤ (N : ℝ) * θ' / (2 * Real.pi) := Nat.floor_le h_nonneg
    have hk2 : (N : ℝ) * θ' / (2 * Real.pi) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    let φ : ℝ := θ' - 2 * Real.pi * (k : ℝ) / (N : ℝ)
    have hφ_nonneg : 0 ≤ φ := by
      dsimp only [φ]
      have hN' : 0 < (N : ℝ) := by exact_mod_cast hN_pos
      have hpi : 0 < 2 * Real.pi := by positivity
      have h : 2 * Real.pi * (k : ℝ) / (N : ℝ) ≤ θ' := by
        calc 2 * Real.pi * (k : ℝ) / (N : ℝ)
            ≤ 2 * Real.pi * ((N : ℝ) * θ' / (2 * Real.pi)) / (N : ℝ) := by gcongr
          _ = θ' := by field_simp [hN'.ne', hpi.ne'] <;> ring
      linarith
    have hφ_lt : φ < 2 * Real.pi / (N : ℝ) := by
      dsimp only [φ]
      have hN' : 0 < (N : ℝ) := by exact_mod_cast hN_pos
      have hpi : 0 < 2 * Real.pi := by positivity
      have h_expand : 2 * Real.pi * ((k : ℝ) + 1) / (N : ℝ) =
          2 * Real.pi * (k : ℝ) / (N : ℝ) + 2 * Real.pi / (N : ℝ) := by
        field_simp [hN'.ne'] <;> ring
      have h : θ' < 2 * Real.pi * ((k : ℝ) + 1) / (N : ℝ) := by
        have h_eq : θ' = 2 * Real.pi * ((N : ℝ) * θ' / (2 * Real.pi)) / (N : ℝ) := by
          field_simp [hN'.ne', hpi.ne'] <;> ring
        have h_lt : 2 * Real.pi * ((N : ℝ) * θ' / (2 * Real.pi)) / (N : ℝ) < 2 * Real.pi * ((k : ℝ) + 1) / (N : ℝ) := by
          apply div_lt_div_of_pos_right _ hN'
          exact mul_lt_mul_of_pos_left hk2 (by positivity)
        rw [h_eq]
        exact h_lt
      rw [h_expand] at h
      linarith
    have h_le_alpha : 2 * Real.pi / (N : ℝ) ≤ α := by
      have h : (2 * Real.pi / α : ℝ) ≤ (N : ℝ) := hN
      have hα' : 0 < α := hα
      have hN' : 0 < (N : ℝ) := by exact_mod_cast hN_pos
      calc 2 * Real.pi / (N : ℝ) ≤ 2 * Real.pi / (2 * Real.pi / α) := by gcongr
        _ = α := by field_simp [hα'.ne', Real.pi_pos.ne'] <;> ring
    have hφ_lt_alpha : φ < α := by linarith
    have h_dist : dist z (f k) < α := by
      have h1 : dist z (f k) = ‖(z : ℂ) - (f k : ℂ)‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]
      rw [h1]
      have h2 : (z : ℂ) = exp (I * θ') := by rw [hz_eq, h_exp_eq]
      rw [h2]
      have h3 : (f k : ℂ) = exp (I * (2 * Real.pi * (k : ℝ) / (N : ℝ))) := by rfl
      rw [h3]
      have h4 : exp (I * θ') - exp (I * (2 * Real.pi * (k : ℝ) / (N : ℝ))) =
          exp (I * (2 * Real.pi * (k : ℝ) / (N : ℝ))) * (exp (I * φ) - 1) := by
        have h5 : θ' = 2 * Real.pi * (k : ℝ) / (N : ℝ) + φ := by
          dsimp only [φ] <;> ring
        have h6 : I * θ' = I * (2 * Real.pi * (k : ℝ) / (N : ℝ)) + I * φ := by
          have h7 : θ' = 2 * Real.pi * (k : ℝ) / (N : ℝ) + φ := h5
          rw [h7]
          simp [mul_add]
          <;> ring
        rw [h6, Complex.exp_add]
        <;> ring
      rw [h4]
      have h6 : ‖exp (I * (2 * Real.pi * (k : ℝ) / (N : ℝ))) * (exp (I * φ) - 1)‖ =
          ‖exp (I * (2 * Real.pi * (k : ℝ) / (N : ℝ)))‖ * ‖exp (I * φ) - 1‖ := norm_mul _ _
      rw [h6]
      have h7 : ‖exp (I * (2 * Real.pi * (k : ℝ) / (N : ℝ)))‖ = 1 := by
        rw [Complex.norm_exp] <;> simp [Complex.mul_re] <;> norm_num
      rw [h7, one_mul]
      have h8 : ‖exp (I * φ) - 1‖ ≤ ‖(φ : ℝ)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      have h9 : ‖(φ : ℝ)‖ = φ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hφ_nonneg]
      rw [h9] at h8
      have h10 : ‖exp (I * φ) - 1‖ < α := by
        calc ‖exp (I * φ) - 1‖ ≤ φ := h8
          _ < α := hφ_lt_alpha
      exact h10
    exact ⟨k, mem_range.mpr hk_lt_N, h_dist⟩
  refine ⟨s, ?_, h_card⟩
  intro z _
  rcases h_main z with ⟨k, hk, hz⟩
  have h_in : f k ∈ s := mem_image.mpr ⟨k, hk, rfl⟩
  exact mem_iUnion₂.mpr ⟨f k, h_in, hz⟩

/-- Cover a Lipschitz image of the unit circle by O(1/α) balls. -/
lemma circle_image_cover {α : ℝ} (hα : 0 < α)
    {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (γ : Circle1 → X) (L : NNReal) (hL_pos : 0 < L)
    (hLipschitz : LipschitzWith L γ) :
    ∃ (s : Finset X),
      Set.range γ ⊆ ⋃ x ∈ s, ball x ((L : ℝ) * α) ∧
      s.card ≤ Nat.ceil (2 * Real.pi / α) := by
  rcases circle_cover_by_balls hα with ⟨s_circle, hcover, hcard⟩
  let s : Finset X := image γ s_circle
  have h_card : s.card ≤ s_circle.card := Finset.card_image_le
  have h_card' : s.card ≤ Nat.ceil (2 * Real.pi / α) := by
    calc s.card ≤ s_circle.card := h_card
      _ ≤ Nat.ceil (2 * Real.pi / α) := hcard
  have h_main : Set.range γ ⊆ ⋃ x ∈ s, ball x ((L : ℝ) * α) := by
    intro y hy
    rcases mem_range.mp hy with ⟨z, rfl⟩
    have hz : z ∈ (Set.univ : Set Circle1) := trivial
    have h9 : z ∈ ⋃ x ∈ s_circle, ball x α := hcover hz
    rcases mem_iUnion₂.mp h9 with ⟨x, hx, hxb⟩
    have h10 : dist (γ z) (γ x) ≤ (L : ℝ) * dist z x := hLipschitz.dist_le_mul z x
    have h11 : dist z x < α := hxb
    have hL_real_pos : 0 < (L : ℝ) := by exact_mod_cast hL_pos
    have h12 : dist (γ z) (γ x) < (L : ℝ) * α := by
      calc dist (γ z) (γ x) ≤ (L : ℝ) * dist z x := h10
        _ < (L : ℝ) * α := by exact mul_lt_mul_of_pos_left h11 hL_real_pos
    have h13 : γ x ∈ s := mem_image.mpr ⟨x, hx, rfl⟩
    exact mem_iUnion₂.mpr ⟨γ x, h13, h12⟩
  exact ⟨s, h_main, h_card'⟩

/-! ## Fiber covering theorem -/

/-- Cover fiber v by O(1/α) balls of radius α. -/
theorem fiber_cover {α : ℝ} (hα : 0 < α) (v : QuatSphere2) :
    ∃ (s : Finset QuatSphere3),
      (fiber v) ⊆ ⋃ x ∈ s, ball x α ∧
      s.card ≤ Nat.ceil (2 * Real.pi / α) := by
  rcases hopfMap_surjective v with ⟨q0, hq0⟩
  let γ : Circle1 → QuatSphere3 := fiberParam v q0 hq0
  have hLipschitz : LipschitzWith 1 γ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have h : ‖(γ x).val - (γ y).val‖ = ‖x.val - y.val‖ := fiberParam_isometry v q0 hq0 x y
    have h2 : dist (γ x) (γ y) = ‖(γ x).val - (γ y).val‖ := by
      have h_dist1 : dist (γ x) (γ y) = dist (γ x).val (γ y).val := by
        exact Subtype.dist_eq (γ x) (γ y)
      rw [h_dist1, dist_eq_norm]
    have h3 : dist x y = ‖x.val - y.val‖ := by
      have h_dist2 : dist x y = dist x.val y.val := by
        exact Subtype.dist_eq x y
      rw [h_dist2, dist_eq_norm]
    calc dist (γ x) (γ y)
        = ‖(γ x).val - (γ y).val‖ := h2
      _ = ‖x.val - y.val‖ := h
      _ = dist x y := h3.symm
      _ ≤ (1 : ℝ) * dist x y := by simp
  have hsurj : fiber v = Set.range γ := fiberParam_surjective v q0 hq0
  classical
  rcases circle_image_cover hα γ 1 (by norm_num) hLipschitz with ⟨s, hcover, hcard⟩
  refine' ⟨s, _ , hcard⟩
  have hcover' : Set.range γ ⊆ ⋃ x ∈ s, ball x α := by
    have h_eq : (↑1 : ℝ) * α = α := by simp
    simpa [h_eq] using hcover
  rw [hsurj]
  exact hcover'

end SeedMathlib.Topology.Homotopy.Pi3Sphere2
