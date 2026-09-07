import MyLeanRepo.Kakeya.Assouad.CinematicBridge
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lower bound on jet gap for slope curve family

This file proves that the jet gap between two slope curves is uniformly
bounded below by a constant times the parameter distance.
-/

noncomputable section

open Kakeya.Cinematic

namespace Kakeya.Assouad

/-- Bound |f(x)| ≤ 2 for x ∈ [0,1] when f(0)=0 and |f'| ≤ 2 on [-1,1]. -/
lemma abs_fx_le_two (f : SlopeFunction) (h_ns : f.IsNonsingular)
    (h0 : f 0 = 0) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |f x| ≤ 2 := by
  have h_diff : Differentiable ℝ f := f.contDiff.differentiable (by norm_num)
  have h_deriv : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (deriv f y) (Set.Icc (0 : ℝ) 1) y := by
    intro y _
    exact h_diff.differentiableAt.hasDerivAt.hasDerivWithinAt
  have h_bound : ∀ y ∈ Set.Icc (0 : ℝ) 1, ‖deriv f y‖₊ ≤ 2 := by
    intro y hy
    have h_y_in : y ∈ Set.Icc (-1 : ℝ) 1 := by
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have h : |deriv f y| ≤ 2 := (h_ns y h_y_in).2.1
    have h_coe : (↑‖deriv f y‖₊ : ℝ) ≤ ↑(2 : NNReal) := by
      have h_eq : (↑‖deriv f y‖₊ : ℝ) = |deriv f y| := by simp
      rw [h_eq]
      <;> norm_num <;> linarith
    exact NNReal.coe_le_coe.mp h_coe
  have h_lip : LipschitzOnWith (2 : NNReal) f (Set.Icc (0 : ℝ) 1) :=
    Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Icc 0 1) h_deriv h_bound
  have h1 : |f x - f 0| ≤ 2 * |x - 0| := h_lip.dist_le_mul x hx 0 (by simp)
  have h2 : f x - f 0 = f x := by rw [h0] <;> ring
  rw [h2] at h1
  have h3 : |x - 0| ≤ 1 := by
    simpa [abs_of_nonneg (show 0 ≤ x from hx.1)] using hx.2
  have h4 : 2 * |x - 0| ≤ 2 := by
    have h5 : |x - 0| ≤ 1 := h3
    linarith
  exact le_trans h1 h4

/--
Core algebraic lemma: given bounds on f, f', f'', the ℓ¹ norm of the
parameter vector is bounded by a constant times the ℓ¹ norm of its image
under the jet matrix A(x).
-/
lemma jetGap_matrix_lower_bound (f_val f' f'' x Δa Δb Δd : ℝ)
    (hf : |f_val| ≤ 2)
    (hfp1 : 1 ≤ |f'|) (hfp2 : |f'| ≤ 2)
    (hfpp : |f''| ≤ 1 / 100)
    (hx1 : 0 ≤ x) (hx2 : x ≤ 1) :
    (99 / 7500 : ℝ) * (|Δa| + |Δb| + |Δd|) ≤
    |Δa + f_val * Δb + x * f_val * Δd| +
    |f' * Δb + (f_val + x * f') * Δd| +
    |f'' * Δb + (2 * f' + x * f'') * Δd| := by
  set D : ℝ := 2 * f'^2 - f_val * f'' with hD
  have h_fp_sq : f'^2 ≥ 1 := by
    have h2 : |f'|^2 = f'^2 := by rw [sq_abs]
    have h : |f'|^2 ≥ 1 := by nlinarith
    rw [h2] at h
    exact h
  have h1 : 2 * f'^2 ≥ 2 := by linarith
  have h_abs_prod : |f_val * f''| ≤ 1 / 50 := by
    calc
      |f_val * f''| = |f_val| * |f''| := by rw [abs_mul]
      _ ≤ 2 * (1 / 100) := by gcongr <;> linarith
      _ = 1 / 50 := by norm_num
  have h_prod_le : f_val * f'' ≤ 1 / 50 := by
    have h5 : f_val * f'' ≤ |f_val * f''| := le_abs_self _
    linarith [h_abs_prod]
  have h_neg_prod_ge : -f_val * f'' ≥ -1 / 50 := by linarith
  have hD_ge : D ≥ 99 / 50 := by
    dsimp only [D]
    linarith
  have hD_pos : 0 < D := by linarith
  set L1 := Δa + f_val * Δb + x * f_val * Δd with hL1
  set L2 := f' * Δb + (f_val + x * f') * Δd with hL2
  set L3 := f'' * Δb + (2 * f' + x * f'') * Δd with hL3
  have hΔb : Δb = (L2 * (2 * f' + x * f'') - L3 * (f_val + x * f')) / D := by
    field_simp [hD, hL2, hL3] <;> ring
  have hΔd : Δd = (f' * L3 - f'' * L2) / D := by
    field_simp [hD, hL2, hL3] <;> ring
  have hΔa : Δa = L1 - f_val * Δb - x * f_val * Δd := by
    rw [hL1] <;> ring
  have h_absx : |x| ≤ 1 := by
    rw [abs_of_nonneg hx1] <;> linarith
  have h_coeff1 : |2 * f' + x * f''| ≤ 401 / 100 := by
    have h1 : |2 * f' + x * f''| ≤ |2 * f'| + |x * f''| := by
      exact abs_add_le (2 * f') (x * f'')
    have h2 : |2 * f'| = 2 * |f'| := by
      rw [abs_mul] <;> simp
    have h3 : |x * f''| = |x| * |f''| := by rw [abs_mul]
    rw [h2, h3] at h1
    have h4 : 2 * |f'| + |x| * |f''| ≤ 401 / 100 := by
      calc
        2 * |f'| + |x| * |f''| ≤ 2 * 2 + 1 * (1 / 100) := by gcongr <;> linarith [h_absx]
        _ = 401 / 100 := by norm_num
    linarith
  have h_coeff2 : |f_val + x * f'| ≤ 4 := by
    have h1 : |f_val + x * f'| ≤ |f_val| + |x * f'| := by
      exact abs_add_le f_val (x * f')
    have h2 : |x * f'| = |x| * |f'| := by rw [abs_mul]
    rw [h2] at h1
    have h3 : |f_val| + |x| * |f'| ≤ 4 := by
      calc
        |f_val| + |x| * |f'| ≤ 2 + 1 * 2 := by gcongr <;> linarith [h_absx]
        _ = 4 := by norm_num
    linarith
  have h_abs_Δb : |Δb| ≤ ((401 / 100 : ℝ) * |L2| + 4 * |L3|) / D := by
    rw [hΔb]
    have h_absD : |D| = D := abs_of_pos hD_pos
    have h1 : |L2 * (2 * f' + x * f'') - L3 * (f_val + x * f')| ≤
        |L2 * (2 * f' + x * f'')| + |L3 * (f_val + x * f')| := by
      exact abs_sub (L2 * (2 * f' + x * f'')) (L3 * (f_val + x * f'))
    have h2 : |L2 * (2 * f' + x * f'')| = |L2| * |2 * f' + x * f''| := by rw [abs_mul]
    have h3 : |L3 * (f_val + x * f')| = |L3| * |f_val + x * f'| := by rw [abs_mul]
    calc
      |(L2 * (2 * f' + x * f'') - L3 * (f_val + x * f')) / D|
        = |L2 * (2 * f' + x * f'') - L3 * (f_val + x * f')| / |D| := by rw [abs_div]
      _ = |L2 * (2 * f' + x * f'') - L3 * (f_val + x * f')| / D := by rw [h_absD]
      _ ≤ (|L2 * (2 * f' + x * f'')| + |L3 * (f_val + x * f')|) / D := by gcongr
      _ = (|L2| * |2 * f' + x * f''| + |L3| * |f_val + x * f'|) / D := by rw [h2, h3] <;> ring
      _ ≤ ((401 / 100 : ℝ) * |L2| + 4 * |L3|) / D := by
        have h4 : |L2| * |2 * f' + x * f''| ≤ (401 / 100 : ℝ) * |L2| := by
          calc
            |L2| * |2 * f' + x * f''| ≤ |L2| * (401 / 100 : ℝ) :=
              mul_le_mul_of_nonneg_left h_coeff1 (abs_nonneg L2)
            _ = (401 / 100 : ℝ) * |L2| := by ring
        have h5 : |L3| * |f_val + x * f'| ≤ 4 * |L3| := by
          calc
            |L3| * |f_val + x * f'| ≤ |L3| * 4 :=
              mul_le_mul_of_nonneg_left h_coeff2 (abs_nonneg L3)
            _ = 4 * |L3| := by ring
        gcongr
        <;> linarith
  have h_abs_Δd : |Δd| ≤ ((1 / 100 : ℝ) * |L2| + 2 * |L3|) / D := by
    rw [hΔd]
    have h_absD : |D| = D := abs_of_pos hD_pos
    have h1 : |f' * L3 - f'' * L2| ≤ |f' * L3| + |f'' * L2| := by
      exact abs_sub (f' * L3) (f'' * L2)
    have h2 : |f' * L3| = |f'| * |L3| := by rw [abs_mul]
    have h3 : |f'' * L2| = |f''| * |L2| := by rw [abs_mul]
    calc
      |(f' * L3 - f'' * L2) / D|
        = |f' * L3 - f'' * L2| / |D| := by rw [abs_div]
      _ = |f' * L3 - f'' * L2| / D := by rw [h_absD]
      _ ≤ (|f' * L3| + |f'' * L2|) / D := by gcongr
      _ = (|f'| * |L3| + |f''| * |L2|) / D := by rw [h2, h3] <;> ring
      _ ≤ (2 * |L3| + (1 / 100 : ℝ) * |L2|) / D := by
        have h4 : |f'| * |L3| ≤ 2 * |L3| := by
          calc
            |f'| * |L3| ≤ 2 * |L3| :=
              mul_le_mul_of_nonneg_right hfp2 (abs_nonneg L3)
            _ = 2 * |L3| := by ring
        have h5 : |f''| * |L2| ≤ (1 / 100 : ℝ) * |L2| := by
          calc
            |f''| * |L2| ≤ (1 / 100 : ℝ) * |L2| :=
              mul_le_mul_of_nonneg_right hfpp (abs_nonneg L2)
            _ = (1 / 100 : ℝ) * |L2| := by ring
        gcongr
        <;> linarith
      _ = ((1 / 100 : ℝ) * |L2| + 2 * |L3|) / D := by ring
  have h_abs_Δa : |Δa| ≤ |L1| + 2 * |Δb| + 2 * |Δd| := by
    rw [hΔa]
    have h1 : |L1 - f_val * Δb - x * f_val * Δd| ≤
        |L1| + |f_val * Δb| + |x * f_val * Δd| := by
      calc
        |L1 - f_val * Δb - x * f_val * Δd|
          = |L1 + (-(f_val * Δb) + (-(x * f_val * Δd)))| := by ring_nf
        _ ≤ |L1| + |-(f_val * Δb) + (-(x * f_val * Δd))| := by
          exact abs_add_le L1 (-(f_val * Δb) + -(x * f_val * Δd))
        _ ≤ |L1| + (|-(f_val * Δb)| + |-(x * f_val * Δd)|) := by
          gcongr
          exact abs_add_le (-(f_val * Δb)) (-(x * f_val * Δd))
        _ = |L1| + |f_val * Δb| + |x * f_val * Δd| := by
          simp [abs_neg] <;> ring
    have h2 : |f_val * Δb| = |f_val| * |Δb| := by rw [abs_mul]
    have h3 : |x * f_val * Δd| = |x| * |f_val| * |Δd| := by
      rw [abs_mul, abs_mul] <;> ring
    rw [h2, h3] at h1
    have h4 : |f_val| ≤ 2 := hf
    have h5 : |x| * |f_val| ≤ 2 := by
      calc
        |x| * |f_val| ≤ 1 * 2 := by gcongr <;> linarith [h_absx]
        _ = 2 := by norm_num
    have h6 : |f_val| * |Δb| ≤ 2 * |Δb| := by
      exact mul_le_mul_of_nonneg_right h4 (abs_nonneg Δb)
    have h7 : |x| * |f_val| * |Δd| ≤ 2 * |Δd| := by
      have h71 : |x| * |f_val| ≤ 2 := h5
      calc
        |x| * |f_val| * |Δd| ≤ 2 * |Δd| := by
          exact mul_le_mul_of_nonneg_right h71 (abs_nonneg Δd)
        _ = 2 * |Δd| := by ring
    have h8 : |L1| + |f_val| * |Δb| + |x| * |f_val| * |Δd| ≤
        |L1| + 2 * |Δb| + 2 * |Δd| := by linarith
    exact le_trans h1 h8
  have h_sum : |Δa| + |Δb| + |Δd| ≤
      |L1| + 3 * |Δb| + 3 * |Δd| := by linarith
  have h_main : |Δa| + |Δb| + |Δd| ≤
      (7500 / 99 : ℝ) * (|L1| + |L2| + |L3|) := by
    calc
      |Δa| + |Δb| + |Δd|
        ≤ |L1| + 3 * |Δb| + 3 * |Δd| := h_sum
      _ ≤ |L1| + 3 * (((401 / 100 : ℝ) * |L2| + 4 * |L3|) / D) +
              3 * (((1 / 100 : ℝ) * |L2| + 2 * |L3|) / D) := by gcongr
      _ = |L1| + (3 / D) * ((402 / 100 : ℝ) * |L2| + 6 * |L3|) := by ring
      _ ≤ |L1| + (3 / D) * (6 * |L2| + 6 * |L3|) := by
        have h6 : (402 / 100 : ℝ) * |L2| ≤ 6 * |L2| := by
          have h7 : (402 / 100 : ℝ) ≤ 6 := by norm_num
          exact mul_le_mul_of_nonneg_right h7 (abs_nonneg L2)
        gcongr
        <;> linarith
      _ = |L1| + (18 / D) * (|L2| + |L3|) := by ring
      _ ≤ |L1| + (18 / (99 / 50 : ℝ)) * (|L2| + |L3|) := by
        have h_div : 18 / D ≤ 18 / (99 / 50 : ℝ) := by
          apply div_le_div_of_nonneg_left
          <;> linarith [hD_ge, hD_pos]
        gcongr
        <;> linarith
      _ = |L1| + (900 / 99 : ℝ) * (|L2| + |L3|) := by norm_num
      _ ≤ (7500 / 99 : ℝ) * (|L1| + |L2| + |L3|) := by
        have h_pos1 : 0 ≤ |L1| := abs_nonneg _
        have h_pos2 : 0 ≤ |L2| := abs_nonneg _
        have h_pos3 : 0 ≤ |L3| := abs_nonneg _
        have h_900 : (900 / 99 : ℝ) ≤ (7500 / 99 : ℝ) := by norm_num
        have h_1 : (1 : ℝ) ≤ (7500 / 99 : ℝ) := by norm_num
        have h_a : |L1| ≤ (7500 / 99 : ℝ) * |L1| := by
          calc
            |L1| = 1 * |L1| := by ring
            _ ≤ (7500 / 99 : ℝ) * |L1| := by
              exact mul_le_mul_of_nonneg_right h_1 h_pos1
        have h_b : (900 / 99 : ℝ) * (|L2| + |L3|) ≤
            (7500 / 99 : ℝ) * (|L2| + |L3|) := by
          exact mul_le_mul_of_nonneg_right h_900 (by linarith)
        have h_final : |L1| + (900 / 99 : ℝ) * (|L2| + |L3|) ≤
            (7500 / 99 : ℝ) * |L1| + (7500 / 99 : ℝ) * (|L2| + |L3|) := by linarith
        have h_eq : (7500 / 99 : ℝ) * |L1| + (7500 / 99 : ℝ) * (|L2| + |L3|) =
            (7500 / 99 : ℝ) * (|L1| + |L2| + |L3|) := by ring
        rw [h_eq] at h_final
        exact h_final
  calc
    (99 / 7500 : ℝ) * (|Δa| + |Δb| + |Δd|)
      ≤ (99 / 7500 : ℝ) * ((7500 / 99 : ℝ) * (|L1| + |L2| + |L3|)) := by gcongr
    _ = |L1| + |L2| + |L3| := by field_simp <;> ring

/-- First derivative of `slopeCurveFunction`. -/
lemma deriv_slopeCurveFunction (f : SlopeFunction) (a b d : ℝ) (t : ℝ) :
    deriv (slopeCurveFunction f a b d) t =
    b * deriv f t + d * (f t + t * deriv f t) := by
  have h_diff : DifferentiableAt ℝ f t :=
    (f.contDiff.differentiable (by norm_num)).differentiableAt
  have h_fd : HasDerivAt f (deriv f t) t := h_diff.hasDerivAt
  have h_id : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h_prod : HasDerivAt (fun x : ℝ => x * f x)
      (1 * f t + t * deriv f t) t := h_id.mul h_fd
  have h_prod' : HasDerivAt (fun x : ℝ => x * f x)
      (f t + t * deriv f t) t := by
    simpa using h_prod
  have h_a : HasDerivAt (fun _ : ℝ => a) 0 t := hasDerivAt_const t a
  have h_b : HasDerivAt (fun x : ℝ => b * f x) (b * deriv f t) t := h_fd.const_mul b
  have h_d : HasDerivAt (fun x : ℝ => d * (x * f x))
      (d * (f t + t * deriv f t)) t := h_prod'.const_mul d
  have h_sum : HasDerivAt (fun x : ℝ => a + b * f x + d * (x * f x))
      (0 + b * deriv f t + d * (f t + t * deriv f t)) t :=
    (h_a.add h_b).add h_d
  have h_main : HasDerivAt (fun x : ℝ => a + b * f x + d * (x * f x))
      (b * deriv f t + d * (f t + t * deriv f t)) t := by
    simpa using h_sum
  have h_eq : (fun x : ℝ => a + b * f x + d * (x * f x)) =
      slopeCurveFunction f a b d := by
    funext x
    simp [slopeCurveFunction] <;> ring
  rw [h_eq] at h_main
  exact h_main.deriv

/-- Second derivative of `slopeCurveFunction`. -/
lemma deriv2_slopeCurveFunction (f : SlopeFunction) (a b d : ℝ) (t : ℝ) :
    deriv (deriv (slopeCurveFunction f a b d)) t =
    b * deriv (deriv f) t + d * (2 * deriv f t + t * deriv (deriv f) t) := by
  have h_diff : Differentiable ℝ f := f.contDiff.differentiable (by norm_num)
  have h_cd1 : ContDiff ℝ 1 (deriv f) := by
    exact f.contDiff.deriv'
  have h_diff2 : Differentiable ℝ (deriv f) := h_cd1.differentiable (by norm_num)
  have h_fd2 : HasDerivAt (deriv f) (deriv (deriv f) t) t :=
    h_diff2.differentiableAt.hasDerivAt
  have h_fd : HasDerivAt f (deriv f t) t :=
    h_diff.differentiableAt.hasDerivAt
  have h_id : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h_prod : HasDerivAt (fun x : ℝ => x * deriv f x)
      (1 * deriv f t + t * deriv (deriv f) t) t := h_id.mul h_fd2
  have h_prod' : HasDerivAt (fun x : ℝ => x * deriv f x)
      (deriv f t + t * deriv (deriv f) t) t := by
    simpa using h_prod
  have h_sum : HasDerivAt (fun x : ℝ => f x + x * deriv f x)
      (deriv f t + (deriv f t + t * deriv (deriv f) t)) t :=
    h_fd.add h_prod'
  have h_b : HasDerivAt (fun x : ℝ => b * deriv f x)
      (b * deriv (deriv f) t) t := h_fd2.const_mul b
  have h_d : HasDerivAt (fun x : ℝ => d * (f x + x * deriv f x))
      (d * (deriv f t + (deriv f t + t * deriv (deriv f) t))) t :=
    h_sum.const_mul d
  have h_main : HasDerivAt (fun x : ℝ => b * deriv f x + d * (f x + x * deriv f x))
      (b * deriv (deriv f) t + d * (deriv f t + (deriv f t + t * deriv (deriv f) t))) t :=
    h_b.add h_d
  have h_main' : HasDerivAt (fun x : ℝ => b * deriv f x + d * (f x + x * deriv f x))
      (b * deriv (deriv f) t + d * (2 * deriv f t + t * deriv (deriv f) t)) t := by
    have h_eq2 : b * deriv (deriv f) t + d * (deriv f t + (deriv f t + t * deriv (deriv f) t)) =
        b * deriv (deriv f) t + d * (2 * deriv f t + t * deriv (deriv f) t) := by ring
    rw [h_eq2] at h_main
    exact h_main
  have h_eq : deriv (slopeCurveFunction f a b d) =
      (fun x : ℝ => b * deriv f x + d * (f x + x * deriv f x)) := by
    funext x
    exact deriv_slopeCurveFunction f a b d x
  have h_main'' : HasDerivAt (deriv (slopeCurveFunction f a b d))
      (b * deriv (deriv f) t + d * (2 * deriv f t + t * deriv (deriv f) t)) t := by
    rw [h_eq]
    exact h_main'
  exact h_main''.deriv

/--
Jet gap lower bound for two slope curves represented by C2Functions.
-/
theorem slopeCurve_jetGap_ge (f : SlopeFunction) (h_ns : f.IsNonsingular)
    (h0 : f 0 = 0)
    (g₁ g₂ : Kakeya.Cinematic.C2Function)
    (a₁ b₁ d₁ a₂ b₂ d₂ : ℝ)
    (h₁ : RepresentsSlopeCurve g₁ f a₁ b₁ d₁)
    (h₂ : RepresentsSlopeCurve g₂ f a₂ b₂ d₂)
    (x : Kakeya.Cinematic.UnitPoint) :
    (99 / 7500 : ℝ) * (|a₁ - a₂| + |b₁ - b₂| + |d₁ - d₂|) ≤
    Kakeya.Cinematic.jetGap g₁ g₂ x := by
  set Δa := a₁ - a₂ with hΔa
  set Δb := b₁ - b₂ with hΔb
  set Δd := d₁ - d₂ with hΔd
  let xv : ℝ := ↑x
  have hx1 : 0 ≤ xv := x.prop.1
  have hx2 : xv ≤ 1 := x.prop.2
  have h_x_in : xv ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨by linarith, by linarith⟩
  have h_fx : |f xv| ≤ 2 := abs_fx_le_two f h_ns h0 (by exact ⟨hx1, hx2⟩)
  have h_fp1 : 1 ≤ |deriv f xv| := (h_ns xv h_x_in).1
  have h_fp2 : |deriv f xv| ≤ 2 := (h_ns xv h_x_in).2.1
  have h_fpp : |deriv (deriv f) xv| ≤ 1 / 100 := (h_ns xv h_x_in).2.2
  have h_val1 : g₁ x - g₂ x = Δa + f xv * Δb + xv * f xv * Δd := by
    have h11 := (h₁ x).1
    have h21 := (h₂ x).1
    simp only [hΔa, hΔb, hΔd, slopeCurveFunction] at *
    <;> linarith
  have h_val2 : g₁.firstDeriv x - g₂.firstDeriv x =
      deriv f xv * Δb + (f xv + xv * deriv f xv) * Δd := by
    have h12 := (h₁ x).2.1
    have h22 := (h₂ x).2.1
    rw [h12, h22]
    rw [deriv_slopeCurveFunction f a₁ b₁ d₁ xv,
        deriv_slopeCurveFunction f a₂ b₂ d₂ xv]
    <;> simp [hΔa, hΔb, hΔd] <;> ring
  have h_val3 : g₁.secondDeriv x - g₂.secondDeriv x =
      deriv (deriv f) xv * Δb +
      (2 * deriv f xv + xv * deriv (deriv f) xv) * Δd := by
    have h13 := (h₁ x).2.2
    have h23 := (h₂ x).2.2
    rw [h13, h23]
    rw [deriv2_slopeCurveFunction f a₁ b₁ d₁ xv,
        deriv2_slopeCurveFunction f a₂ b₂ d₂ xv]
    <;> simp [hΔa, hΔb, hΔd] <;> ring
  have h_main := jetGap_matrix_lower_bound (f xv) (deriv f xv)
    (deriv (deriv f) xv) xv Δa Δb Δd h_fx h_fp1 h_fp2 h_fpp hx1 hx2
  simpa [Kakeya.Cinematic.jetGap, h_val1, h_val2, h_val3] using h_main

end Kakeya.Assouad
